//! rm-gpu — GPU accelerator interface for WalkSAT phase guidance.
//!
//! Defines the `GpuAccelerator` trait and a `CpuFallback` reference
//! implementation.  The Metal backend (`feature = "metal"`) provides
//! 10 000-trajectory parallel WalkSAT on Apple Silicon unified memory.

#[cfg(feature = "metal")]
pub mod metal_backend;
#[cfg(feature = "metal")]
pub use metal_backend::MetalAccelerator;

// ---------------------------------------------------------------------------
// Shared clause representation
// ---------------------------------------------------------------------------

/// A clause in DIMACS-signed form: positive integer = positive literal,
/// negative integer = negative literal (1-indexed variables).
pub struct GpuClause {
    pub lits: Vec<i32>,
}

// ---------------------------------------------------------------------------
// Walk result
// ---------------------------------------------------------------------------

/// Output from a WalkSAT run: the best polarity seen and how many clauses
/// it satisfies.
pub struct WalkResult {
    /// polarity[0..=num_vars]; index 0 is unused (variable numbering starts at 1).
    pub polarity: Vec<bool>,
    /// Number of clauses satisfied by `polarity`.
    pub sat_count: usize,
}

// ---------------------------------------------------------------------------
// Trait
// ---------------------------------------------------------------------------

pub trait GpuAccelerator: Send + Sync {
    /// Run parallel WalkSAT trajectories and return the best polarity found.
    ///
    /// * `clauses` — formula as DIMACS-signed clause list
    /// * `num_vars` — highest variable index; variables are 1..=num_vars
    /// * `initial_polarity` — starting polarity slice of length ≥ num_vars+1
    /// * `seed` — deterministic seed (derived from solver state)
    /// * `num_trajectories` — number of independent walks (GPU: 10 000; CPU: 1)
    /// * `steps_per_var` — steps = num_vars × steps_per_var per trajectory
    fn walk(
        &self,
        clauses: &[GpuClause],
        num_vars: u32,
        initial_polarity: &[bool],
        seed: u64,
        num_trajectories: u32,
        steps_per_var: u32,
    ) -> WalkResult;

    fn device_name(&self) -> &str;
}

// ---------------------------------------------------------------------------
// Occurrence list helper
// ---------------------------------------------------------------------------

/// Build occurrence lists from a clause list.
///
/// Returns `occ` where `occ[lit_raw]` is the list of clause indices that
/// contain that literal.  The raw index for variable `v` is:
///   positive literal → `v * 2`
///   negative literal → `v * 2 + 1`
pub fn build_occurrence_lists(clauses: &[GpuClause], num_vars: u32) -> Vec<Vec<u32>> {
    let cap = (num_vars as usize + 1) * 2;
    let mut occ: Vec<Vec<u32>> = vec![Vec::new(); cap];
    for (ci, c) in clauses.iter().enumerate() {
        for &lit in &c.lits {
            let var = lit.unsigned_abs() as usize;
            if var == 0 || var > num_vars as usize {
                continue;
            }
            let raw = var * 2 + if lit < 0 { 1 } else { 0 };
            if raw < cap {
                occ[raw].push(ci as u32);
            }
        }
    }
    occ
}

// ---------------------------------------------------------------------------
// CPU fallback (single-trajectory WalkSAT)
// ---------------------------------------------------------------------------

pub struct CpuFallback;

impl GpuAccelerator for CpuFallback {
    fn walk(
        &self,
        clauses: &[GpuClause],
        num_vars: u32,
        initial_polarity: &[bool],
        seed: u64,
        _num_trajectories: u32,
        steps_per_var: u32,
    ) -> WalkResult {
        let n = num_vars as usize;
        let nc = clauses.len();

        if nc == 0 || n == 0 {
            return WalkResult {
                polarity: vec![false; n + 1],
                sat_count: 0,
            };
        }

        let occ = build_occurrence_lists(clauses, num_vars);
        let max_steps = n * steps_per_var as usize;

        // Start from the provided initial polarity; ensure slice is long enough.
        let mut wa: Vec<bool> = vec![false; n + 1];
        for v in 1..=n {
            if v < initial_polarity.len() {
                wa[v] = initial_polarity[v];
            }
        }

        // Per-clause satisfaction count.
        let mut sat_count: Vec<u8> = clauses
            .iter()
            .map(|c| {
                c.lits
                    .iter()
                    .filter(|&&l| {
                        let v = l.unsigned_abs() as usize;
                        v >= 1 && v <= n && (l > 0) == wa[v]
                    })
                    .count()
                    .min(255) as u8
            })
            .collect();

        let mut total_sat: usize = sat_count.iter().filter(|&&s| s > 0).count();
        let initial_score = total_sat;
        let mut best_score = total_sat;
        let mut best_phase = wa.clone();

        // LCG RNG (same constants as the Metal kernel for determinism testing).
        let mut rng: u64 = seed;

        let mut steps_since_improvement = 0usize;
        const WALK_EARLY_EXIT: usize = 500;

        'walk: for _ in 0..max_steps {
            // Pick a random unsatisfied clause (retry once).
            rng = rng
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let mut ci = (rng >> 33) as usize % nc;
            if sat_count[ci] > 0 {
                rng = rng
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                ci = (rng >> 33) as usize % nc;
                if sat_count[ci] > 0 {
                    continue;
                }
            }
            let clause = &clauses[ci].lits;
            if clause.is_empty() {
                continue;
            }

            // 15% noise: random flip from the clause.
            rng = rng
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let noise = (rng >> 33) % 100 < 15;

            let flip_var: usize;
            if noise {
                rng = rng
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                let pick = (rng >> 33) as usize % clause.len();
                let v = clause[pick].unsigned_abs() as usize;
                if v == 0 || v > n {
                    continue;
                }
                flip_var = v;
            } else {
                // Greedy: minimum break count.
                let mut best_v = 0usize;
                let mut min_break = usize::MAX;
                for &lit in clause {
                    let v = lit.unsigned_abs() as usize;
                    if v == 0 || v > n {
                        continue;
                    }
                    let cur_raw = v * 2 + if wa[v] { 0 } else { 1 };
                    let brk: usize = occ[cur_raw]
                        .iter()
                        .filter(|&&c| sat_count[c as usize] == 1)
                        .count();
                    if brk < min_break {
                        min_break = brk;
                        best_v = v;
                    }
                    if min_break == 0 {
                        break;
                    }
                }
                if best_v == 0 {
                    continue;
                }
                flip_var = best_v;
            }

            // Perform flip and update sat_count incrementally.
            let old_raw = flip_var * 2 + if wa[flip_var] { 0 } else { 1 };
            wa[flip_var] = !wa[flip_var];
            let new_raw = flip_var * 2 + if wa[flip_var] { 0 } else { 1 };

            for &c in &occ[old_raw] {
                let c = c as usize;
                if sat_count[c] == 1 {
                    total_sat -= 1;
                }
                sat_count[c] = sat_count[c].saturating_sub(1);
            }
            for &c in &occ[new_raw] {
                let c = c as usize;
                if sat_count[c] == 0 {
                    total_sat += 1;
                }
                sat_count[c] = sat_count[c].saturating_add(1);
            }

            if total_sat > best_score {
                best_score = total_sat;
                best_phase = wa.clone();
                steps_since_improvement = 0;
            } else {
                steps_since_improvement += 1;
                if steps_since_improvement >= WALK_EARLY_EXIT {
                    break 'walk;
                }
            }
        }

        // Report best found; use initial_score to let caller decide whether
        // to write back (consistent with the CPU walk_phase guard).
        let _ = initial_score;

        WalkResult {
            polarity: best_phase,
            sat_count: best_score,
        }
    }

    fn device_name(&self) -> &str {
        "cpu-fallback"
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn make_simple_clauses() -> Vec<GpuClause> {
        // (x1 ∨ x2) ∧ (¬x1 ∨ x3) ∧ (¬x2 ∨ ¬x3)
        vec![
            GpuClause { lits: vec![1, 2] },
            GpuClause { lits: vec![-1, 3] },
            GpuClause { lits: vec![-2, -3] },
        ]
    }

    #[test]
    fn cpu_fallback_finds_solution() {
        let clauses = make_simple_clauses();
        let polarity = vec![false; 4];
        let result = CpuFallback.walk(&clauses, 3, &polarity, 42, 1, 64);
        assert_eq!(result.sat_count, 3, "CpuFallback should satisfy all clauses for SAT formula");
    }

    #[test]
    fn cpu_fallback_unsat_makes_progress() {
        // PHP(2,1): pigeon hole principle, UNSAT.
        // (x1 ∨ x2) ∧ (¬x1) ∧ (¬x2) — at most 2 of 3 clauses satisfiable
        let clauses = vec![
            GpuClause { lits: vec![1, 2] },
            GpuClause { lits: vec![-1] },
            GpuClause { lits: vec![-2] },
        ];
        let polarity = vec![false; 3];
        let result = CpuFallback.walk(&clauses, 2, &polarity, 42, 1, 64);
        assert!(result.sat_count >= 2, "should satisfy ≥2 clauses (max possible for UNSAT)");
    }

    #[test]
    fn build_occ_lists_correct() {
        let clauses = make_simple_clauses();
        let occ = build_occurrence_lists(&clauses, 3);
        // Positive literal of var 1 (raw = 2): appears in clause 0
        assert!(occ[1 * 2].contains(&0), "x1 should appear in clause 0");
        // Negative literal of var 1 (raw = 3): appears in clause 1
        assert!(occ[1 * 2 + 1].contains(&1), "¬x1 should appear in clause 1");
        // Negative literal of var 2 (raw = 5): appears in clause 2
        assert!(occ[2 * 2 + 1].contains(&2), "¬x2 should appear in clause 2");
    }

    #[test]
    fn cpu_fallback_respects_initial_polarity() {
        // Formula where polarity [false, true, false, false] already satisfies all 3 clauses.
        // (x1 ∨ x2): x2=true satisfies
        // (¬x1 ∨ x3): ¬x1 satisfies (x1=false)
        // (¬x2 ∨ ¬x3): ¬x3 satisfies (x3=false)
        let clauses = make_simple_clauses();
        let polarity = vec![false, true, false, false];
        let result = CpuFallback.walk(&clauses, 3, &polarity, 123, 1, 4);
        assert_eq!(result.sat_count, 3, "starting from a satisfying polarity should stay at 3");
    }

    #[cfg(feature = "metal")]
    #[test]
    fn metal_matches_or_beats_cpu_score_on_sat() {
        use crate::MetalAccelerator;
        let clauses = make_simple_clauses();
        let polarity = vec![false; 4];
        let metal = MetalAccelerator::new().expect("Metal not available");
        let result = metal.walk(&clauses, 3, &polarity, 42, 100, 16);
        assert_eq!(
            result.sat_count, 3,
            "Metal should satisfy all clauses for SAT formula with 100 trajectories"
        );
    }
}
