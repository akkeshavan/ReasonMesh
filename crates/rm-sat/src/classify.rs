//! Instance classification: structural feature extraction and rule-based class detection.
//!
//! Phase 1 of algorithm selection: a single O(n+m) pass over the clause list extracts
//! a small feature vector, which is then mapped to a coarse DetectedClass by a
//! hand-tuned decision tree. No ML, no search-phase probing.

use crate::dimacs::DimacsCnf;
use crate::xor::xor_density_approx;
use serde::{Deserialize, Serialize};

/// Coarse problem class inferred from structural features.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DetectedClass {
    /// Uniform random 3-SAT near the phase transition (~4.27 ratio).
    Random3Sat,
    /// Dominated by at-most-one / cardinality constraints (e.g. PHP).
    CardinalityHeavy,
    /// Circuit-like: binary-clause fraction > 50%, gate structure.
    CircuitLike,
    /// XOR-heavy: high fraction of clauses form XOR pairs/triples (e.g. crypto).
    XorHeavy,
    /// Planning-like: Horn fraction > 65% (≤1 positive literal per clause).
    PlanningLike,
    /// Highly symmetric: coefficient of variation of variable degrees is very low.
    SymmetryHeavy,
    /// Industrial / over-constrained: many unit clauses, low ratio.
    Industrial,
    /// Default when no single class dominates.
    Mixed,
}

impl std::fmt::Display for DetectedClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Random3Sat => "random-3sat",
            Self::CardinalityHeavy => "cardinality-heavy",
            Self::CircuitLike => "circuit-like",
            Self::XorHeavy => "xor-heavy",
            Self::PlanningLike => "planning-like",
            Self::SymmetryHeavy => "symmetry-heavy",
            Self::Industrial => "industrial",
            Self::Mixed => "mixed",
        };
        write!(f, "{s}")
    }
}

/// Structural profile of a CNF instance extracted in O(n + m) time.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct InstanceProfile {
    pub num_vars: u32,
    pub num_clauses: usize,
    /// Clause-to-variable ratio (m / n).
    pub clause_ratio: f32,
    /// Fraction of unit clauses (length 1).
    pub frac_unit: f32,
    /// Fraction of binary clauses (length 2).
    pub frac_binary: f32,
    /// Fraction of ternary clauses (length 3).
    pub frac_ternary: f32,
    /// Fraction of Horn clauses (≤1 positive literal).
    pub frac_horn: f32,
    /// Among binary clauses: fraction where both literals are negative.
    /// High value = pairwise AMO (at-most-one) encoding.
    pub amo_density: f32,
    /// Symmetry score in [0, 1]: 1.0 = perfectly uniform variable degrees, 0.0 = highly skewed.
    /// Computed as 1 / (1 + CV) where CV = stddev / mean of per-variable occurrence counts.
    pub symmetry_score: f32,
    /// Fraction of variables forced by initial unit propagation (backbone lower bound).
    pub backbone_lower: f32,
    /// Fraction of clauses that participate in detected binary XOR constraints.
    pub xor_density: f32,
    /// Inferred problem class.
    pub detected_class: DetectedClass,
}

impl std::fmt::Display for InstanceProfile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "class={} vars={} clauses={} ratio={:.2} horn={:.2} binary={:.2} amo={:.2} xor={:.2} sym={:.2} backbone={:.2}",
            self.detected_class,
            self.num_vars,
            self.num_clauses,
            self.clause_ratio,
            self.frac_horn,
            self.frac_binary,
            self.amo_density,
            self.xor_density,
            self.symmetry_score,
            self.backbone_lower,
        )
    }
}

/// Analyse a parsed CNF instance and return its structural profile.
pub fn analyse(cnf: &DimacsCnf) -> InstanceProfile {
    let n = cnf.num_vars as usize;
    let m = cnf.clauses.len();

    if n == 0 || m == 0 {
        return InstanceProfile {
            num_vars: cnf.num_vars,
            num_clauses: m,
            clause_ratio: 0.0,
            frac_unit: 0.0,
            frac_binary: 0.0,
            frac_ternary: 0.0,
            frac_horn: 0.0,
            amo_density: 0.0,
            symmetry_score: 1.0,
            backbone_lower: 0.0,
            xor_density: 0.0,
            detected_class: DetectedClass::Industrial,
        };
    }

    let mut unit_count = 0usize;
    let mut binary_count = 0usize;
    let mut ternary_count = 0usize;
    let mut horn_count = 0usize;
    let mut amo_binary_count = 0usize;
    let mut var_occ = vec![0u32; n + 1];
    let mut forced = vec![false; n + 1];

    for clause in &cnf.clauses {
        let len = clause.len();
        match len {
            0 => {}
            1 => {
                unit_count += 1;
                let var = clause[0].unsigned_abs() as usize;
                if var <= n {
                    forced[var] = true;
                }
            }
            2 => {
                binary_count += 1;
                if clause[0] < 0 && clause[1] < 0 {
                    amo_binary_count += 1;
                }
            }
            3 => ternary_count += 1,
            _ => {}
        }

        let mut pos = 0u32;
        for &lit in clause {
            let var = lit.unsigned_abs() as usize;
            if var <= n {
                var_occ[var] += 1;
            }
            if lit > 0 {
                pos += 1;
            }
        }
        if pos <= 1 {
            horn_count += 1;
        }
    }

    let mf = m as f32;
    let frac_unit = unit_count as f32 / mf;
    let frac_binary = binary_count as f32 / mf;
    let frac_ternary = ternary_count as f32 / mf;
    let frac_horn = horn_count as f32 / mf;
    let amo_density = if binary_count > 0 {
        amo_binary_count as f32 / binary_count as f32
    } else {
        0.0
    };
    let clause_ratio = mf / n as f32;

    let occ = &var_occ[1..=n];
    let mean_occ = occ.iter().sum::<u32>() as f32 / n as f32;
    let symmetry_score = if mean_occ > 0.0 {
        let variance = occ
            .iter()
            .map(|&o| {
                let d = o as f32 - mean_occ;
                d * d
            })
            .sum::<f32>()
            / n as f32;
        let cv = variance.sqrt() / mean_occ;
        1.0 / (1.0 + cv)
    } else {
        1.0
    };

    let backbone_lower = forced[1..=n].iter().filter(|&&b| b).count() as f32 / n as f32;
    let xor_density = xor_density_approx(cnf);

    let detected_class = classify_features(
        clause_ratio,
        frac_unit,
        frac_binary,
        frac_ternary,
        frac_horn,
        amo_density,
        symmetry_score,
        xor_density,
    );

    InstanceProfile {
        num_vars: cnf.num_vars,
        num_clauses: m,
        clause_ratio,
        frac_unit,
        frac_binary,
        frac_ternary,
        frac_horn,
        amo_density,
        symmetry_score,
        backbone_lower,
        xor_density,
        detected_class,
    }
}

fn classify_features(
    clause_ratio: f32,
    frac_unit: f32,
    frac_binary: f32,
    frac_ternary: f32,
    frac_horn: f32,
    amo_density: f32,
    symmetry_score: f32,
    xor_density: f32,
) -> DetectedClass {
    // Industrial: many unit clauses → already heavily constrained
    if frac_unit > 0.15 {
        return DetectedClass::Industrial;
    }
    // Binary-dominated: split on what the binary clauses encode.
    // AMO pairs (¬x ∨ ¬y) indicate cardinality constraints (e.g. PHP).
    // XOR pairs (mixed signs, complementary) indicate parity/crypto.
    // Mixed-sign non-XOR binary clauses indicate circuit implications.
    if frac_binary > 0.30 {
        if amo_density > 0.60 {
            return DetectedClass::CardinalityHeavy;
        }
        if xor_density > 0.30 {
            return DetectedClass::XorHeavy;
        }
        if frac_binary > 0.50 {
            return DetectedClass::CircuitLike;
        }
    }
    // XOR-heavy even without dominating binary fraction (e.g. XOR-SAT problems)
    if xor_density > 0.40 {
        return DetectedClass::XorHeavy;
    }
    // Planning-like: predominantly Horn clauses
    if frac_horn > 0.65 {
        return DetectedClass::PlanningLike;
    }
    // Random 3-SAT: ternary-dominated near the phase transition
    if frac_ternary > 0.60 && clause_ratio >= 3.5 && clause_ratio <= 5.5 {
        return DetectedClass::Random3Sat;
    }
    // Symmetry-heavy: very uniform degree distribution
    if symmetry_score > 0.88 {
        return DetectedClass::SymmetryHeavy;
    }
    DetectedClass::Mixed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dimacs::parse_dimacs;

    fn php_unsat(pigeons: u32, holes: u32) -> DimacsCnf {
        // Standard PHP encoding: pigeons × holes vars,
        // "each pigeon in some hole" + "each hole at most one pigeon"
        let n = pigeons * holes;
        let mut clauses: Vec<Vec<i32>> = Vec::new();
        let var = |p: u32, h: u32| -> i32 { (p * holes + h + 1) as i32 };
        for p in 0..pigeons {
            clauses.push((0..holes).map(|h| var(p, h)).collect());
        }
        for h in 0..holes {
            for p1 in 0..pigeons {
                for p2 in (p1 + 1)..pigeons {
                    clauses.push(vec![-var(p1, h), -var(p2, h)]);
                }
            }
        }
        DimacsCnf {
            num_vars: n,
            clauses,
        }
    }

    #[test]
    fn php_classified_as_cardinality_heavy() {
        let cnf = php_unsat(5, 4);
        let p = analyse(&cnf);
        // PHP has many AMO binary clauses
        assert!(
            p.amo_density > 0.5,
            "expected high amo_density, got {:.2}",
            p.amo_density
        );
        assert_eq!(p.detected_class, DetectedClass::CardinalityHeavy);
    }

    #[test]
    fn random_3sat_classified_correctly() {
        // Near-phase-transition 3-SAT: all clauses are ternary, ratio ~4.27
        let raw = "p cnf 50 213\n";
        let mut dimacs = raw.to_string();
        // Build 213 ternary clauses over 50 variables
        for i in 0..213usize {
            let a = (i % 50 + 1) as i32;
            let b = ((i * 7 + 3) % 50 + 1) as i32;
            let c = ((i * 13 + 7) % 50 + 1) as i32;
            let sa = if i % 3 == 0 { -1 } else { 1 };
            let sb = if i % 5 == 0 { -1 } else { 1 };
            let sc = if i % 7 == 0 { -1 } else { 1 };
            dimacs.push_str(&format!("{} {} {} 0\n", sa * a, sb * b, sc * c));
        }
        let cnf = parse_dimacs(&dimacs).unwrap();
        let p = analyse(&cnf);
        assert!(p.frac_ternary > 0.8);
        assert!(p.clause_ratio > 3.5 && p.clause_ratio < 5.5);
        assert_eq!(p.detected_class, DetectedClass::Random3Sat);
    }

    #[test]
    fn display_is_informative() {
        let cnf = php_unsat(4, 3);
        let p = analyse(&cnf);
        let s = p.to_string();
        assert!(s.contains("class="), "display should include class=");
        assert!(s.contains("ratio="), "display should include ratio=");
    }
}
