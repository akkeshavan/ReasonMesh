//! Parallel CDCL with shared learned-clause database.
//!
//! # Architecture
//!
//! Each thread runs a full `CdclSolver` instance over the same original problem.
//! Threads operate in fixed-length *conflict slices* (default: 1 000 conflicts).
//! Between slices every thread:
//!
//!   1. **Exports** high-quality learned clauses (LBD ≤ threshold) to a shared,
//!      mutex-protected pool.
//!   2. **Imports** all clauses added since its last import watermark.
//!
//! The first thread to find SAT or UNSAT wins; a shared cancel flag stops all others.
//!
//! # Thread diversity
//!
//! Pure portfolio parallelism (run the same solver N times) gains nothing beyond
//! luck. Diversity is injected via:
//!
//! - **Polarity bias**: even threads prefer TRUE branches; odd threads prefer FALSE.
//! - **Luby restart scale**: staggered so threads restart at different conflict counts.
//! - **Activity noise**: a thread-specific multiplicative bump applied at startup
//!   breaks symmetry in the initial VSIDS heap ordering.
//!
//! # Scaling hypotheses (experimental program)
//!
//! H1  Single big machine (34 cores / 256 GB): parallel CDCL with shared clause DB.
//!     Measure: speedup vs sequential, crossover problem size S* where sharing helps.
//! H2  Big machine + RPi cluster: big machine as orchestrator / cube generator,
//!     Pi nodes as leaf solvers.
//! H3  100-node RPi cluster without big machine.
//! H4  1 000-node cluster.

use std::sync::{
    atomic::{AtomicBool, Ordering},
    mpsc, Arc, Mutex,
};
use std::thread;

use rm_akx::literal::Literal;

use crate::{CdclSolver, SolveResult};

// ---------------------------------------------------------------------------
// Tuning constants (overridable via ParallelConfig)
// ---------------------------------------------------------------------------

/// Default number of conflicts per work-slice before import/export.
/// Lower → more sharing but more lock contention. 1 000 is a good baseline.
const DEFAULT_SLICE_CONFLICTS: u64 = 1_000;

/// Default LBD threshold for clause export. Clauses with LBD ≤ 6 are "good".
/// LBD ≤ 2 ("glue clauses") are always worth sharing; 6 is a conservative upper bound.
const DEFAULT_LBD_THRESHOLD: u8 = 6;

/// Hard cap on the shared DB size. When exceeded the oldest 25 % are evicted.
/// 100 000 clauses × ~20 bytes average = ~2 MB resident — negligible.
const DEFAULT_MAX_SHARED: usize = 100_000;

// ---------------------------------------------------------------------------
// SharedClauseDb
// ---------------------------------------------------------------------------

/// One clause in the shared pool.
struct SharedEntry {
    /// Raw literal values (Literal::raw()) so Send + Sync is trivial.
    lits: Vec<u32>,
    lbd: u8,
}

struct DbInner {
    entries: Vec<SharedEntry>,
    /// Total entries ever evicted from the front (the absolute sequence base).
    base: usize,
}

/// Thread-safe, append-only (with bounded eviction) shared learned clause pool.
///
/// Each thread tracks a *watermark* — the absolute sequence number up to which
/// it has already imported.  When entries are evicted from the front, `base`
/// is incremented so that `base + entries[i]` gives the absolute sequence number
/// of the i-th current entry.  This prevents the watermark from going out of
/// bounds after eviction.
pub struct SharedClauseDb {
    inner: Mutex<DbInner>,
    lbd_threshold: u8,
    max_clauses: usize,
}

impl SharedClauseDb {
    pub fn new(lbd_threshold: u8, max_clauses: usize) -> Self {
        Self {
            inner: Mutex::new(DbInner { entries: Vec::new(), base: 0 }),
            lbd_threshold,
            max_clauses,
        }
    }

    /// Attempt to add a learned clause to the pool.
    /// Silently dropped when `lbd > threshold` or the clause is unit (lbd==1 is
    /// always accepted — unit facts are high-value).
    pub fn export(&self, lits: &[Literal], lbd: u8) {
        if lbd > self.lbd_threshold { return; }
        if lits.is_empty() { return; }
        let raw: Vec<u32> = lits.iter().map(|l| l.raw()).collect();
        let mut g = self.inner.lock().unwrap();
        if g.entries.len() >= self.max_clauses {
            // Evict oldest 25 % to keep memory bounded.
            let evict = g.entries.len() / 4;
            g.entries.drain(0..evict);
            g.base += evict;
        }
        g.entries.push(SharedEntry { lits: raw, lbd });
    }

    /// Return all clauses added since `*watermark`, updating the watermark.
    ///
    /// The watermark is an *absolute sequence number*.  If entries that the
    /// caller hadn't yet imported were evicted, they are silently skipped (the
    /// solver misses those learned clauses but remains correct).
    pub fn import_since(&self, watermark: &mut usize) -> Vec<Vec<Literal>> {
        let g = self.inner.lock().unwrap();
        // Convert the absolute watermark to a relative index, clamped so it
        // never exceeds the current slice.
        let start = watermark.saturating_sub(g.base).min(g.entries.len());
        let new: Vec<Vec<Literal>> = g.entries[start..]
            .iter()
            .map(|e| e.lits.iter().map(|&r| Literal::from_raw(r)).collect())
            .collect();
        *watermark = g.base + g.entries.len();
        new
    }

    /// Current number of stored clauses (diagnostic / stats).
    pub fn len(&self) -> usize {
        self.inner.lock().unwrap().entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for a parallel solve run.
pub struct ParallelConfig {
    /// Number of worker threads. `0` means "use all logical CPUs".
    pub num_threads: usize,
    /// Only export clauses with LBD ≤ this value.
    pub lbd_export_threshold: u8,
    /// Conflicts per solve-slice before import/export round.
    pub slice_conflicts: u64,
    /// Hard cap on the shared clause pool.
    pub max_shared_clauses: usize,
}

impl Default for ParallelConfig {
    fn default() -> Self {
        let cpus = thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4);
        Self {
            num_threads: cpus,
            lbd_export_threshold: DEFAULT_LBD_THRESHOLD,
            slice_conflicts: DEFAULT_SLICE_CONFLICTS,
            max_shared_clauses: DEFAULT_MAX_SHARED,
        }
    }
}

// ---------------------------------------------------------------------------
// ParallelCdclSolver
// ---------------------------------------------------------------------------

/// Parallel CDCL solver: N threads share one clause pool, first to finish wins.
pub struct ParallelCdclSolver {
    num_vars: u32,
    /// Original (non-learned) clauses, stored as raw Literals.
    clauses: Arc<Vec<Vec<Literal>>>,
    config: ParallelConfig,
}

impl ParallelCdclSolver {
    /// Build from a DIMACS-parsed problem. Clauses are signed integer literals
    /// as returned by `parse_dimacs` (var = lit.unsigned_abs(), positive iff lit > 0).
    pub fn from_dimacs(num_vars: u32, dimacs_clauses: &[Vec<i32>], config: ParallelConfig) -> Self {
        let clauses: Vec<Vec<Literal>> = dimacs_clauses
            .iter()
            .map(|cl| {
                cl.iter()
                    .map(|&lit| {
                        let var = lit.unsigned_abs();
                        if lit > 0 {
                            Literal::positive(var)
                        } else {
                            Literal::negative(var)
                        }
                    })
                    .collect()
            })
            .collect();
        Self {
            num_vars,
            clauses: Arc::new(clauses),
            config,
        }
    }

    /// Solve using all configured worker threads.
    /// Returns the first SAT/UNSAT result; all remaining threads are cancelled.
    pub fn solve(&self) -> SolveResult {
        let n = if self.config.num_threads == 0 {
            thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4)
        } else {
            self.config.num_threads
        };

        let shared_db = Arc::new(SharedClauseDb::new(
            self.config.lbd_export_threshold,
            self.config.max_shared_clauses,
        ));
        let cancel = Arc::new(AtomicBool::new(false));
        let (tx, rx) = mpsc::channel::<SolveResult>();

        let handles: Vec<_> = (0..n)
            .map(|tid| {
                let clauses = Arc::clone(&self.clauses);
                let db = Arc::clone(&shared_db);
                let cancel = Arc::clone(&cancel);
                let tx = tx.clone();
                let num_vars = self.num_vars;
                let slice = self.config.slice_conflicts;
                thread::spawn(move || {
                    worker(tid, num_vars, &clauses, &db, &cancel, slice, tx);
                })
            })
            .collect();

        // Drop the original sender so the channel closes when all workers exit.
        drop(tx);

        let result = rx.recv().unwrap_or(SolveResult::Unknown);
        cancel.store(true, Ordering::Relaxed);
        for h in handles {
            let _ = h.join();
        }
        result
    }

    /// Like `solve`, but stops early when `external_cancel` is set.
    /// Used by cluster worker nodes to honour coordinator-driven cancellation.
    pub fn solve_with_cancel(&self, external_cancel: Arc<AtomicBool>) -> SolveResult {
        let n = if self.config.num_threads == 0 {
            thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4)
        } else {
            self.config.num_threads
        };

        let shared_db = Arc::new(SharedClauseDb::new(
            self.config.lbd_export_threshold,
            self.config.max_shared_clauses,
        ));
        let cancel = Arc::new(AtomicBool::new(false));
        let (tx, rx) = mpsc::channel::<SolveResult>();

        let handles: Vec<_> = (0..n)
            .map(|tid| {
                let clauses = Arc::clone(&self.clauses);
                let db = Arc::clone(&shared_db);
                let cancel = Arc::clone(&cancel);
                let ext = Arc::clone(&external_cancel);
                let tx = tx.clone();
                let num_vars = self.num_vars;
                let slice = self.config.slice_conflicts;
                thread::spawn(move || {
                    worker_ext(tid, num_vars, &clauses, &db, &cancel, &ext, slice, tx);
                })
            })
            .collect();

        drop(tx);
        let result = rx.recv().unwrap_or(SolveResult::Unknown);
        cancel.store(true, Ordering::Relaxed);
        for h in handles {
            let _ = h.join();
        }
        result
    }
}

// ---------------------------------------------------------------------------
// Worker
// ---------------------------------------------------------------------------

fn worker(
    thread_id: usize,
    num_vars: u32,
    clauses: &[Vec<Literal>],
    shared_db: &SharedClauseDb,
    cancel: &AtomicBool,
    slice_conflicts: u64,
    tx: mpsc::Sender<SolveResult>,
) {
    let mut solver = build_diverse_solver(num_vars, clauses, thread_id);
    let mut watermark: usize = 0;

    loop {
        if cancel.load(Ordering::Relaxed) {
            return;
        }

        // ---- Solve one conflict slice ----
        match solver.solve(&[], slice_conflicts) {
            SolveResult::Sat(model) => {
                let _ = tx.send(SolveResult::Sat(model));
                return;
            }
            SolveResult::Unsat => {
                let _ = tx.send(SolveResult::Unsat);
                return;
            }
            // Budget hit: do import/export then continue.
            SolveResult::BudgetExceeded => {}
            // Solver signalled it can't continue (e.g. external cancel check
            // inside the loop if we add one later).
            SolveResult::Unknown => return,
        }

        // ---- Export high-quality learned clauses ----
        for (lits, lbd) in solver.drain_learned() {
            shared_db.export(&lits, lbd as u8);
        }

        // ---- Import new clauses from other threads ----
        let new_clauses = shared_db.import_since(&mut watermark);
        if !new_clauses.is_empty() {
            // import_clauses() backtracks to level 0 first (safe after BudgetExceeded
            // which already returns the solver to base_level).
            solver.import_clauses(&new_clauses);
        }
    }
}

/// Like `worker` but also checks an external cancel flag set by the cluster layer.
fn worker_ext(
    thread_id: usize,
    num_vars: u32,
    clauses: &[Vec<Literal>],
    shared_db: &SharedClauseDb,
    cancel: &AtomicBool,
    external_cancel: &AtomicBool,
    slice_conflicts: u64,
    tx: mpsc::Sender<SolveResult>,
) {
    let mut solver = build_diverse_solver(num_vars, clauses, thread_id);
    let mut watermark: usize = 0;

    loop {
        if cancel.load(Ordering::Relaxed) || external_cancel.load(Ordering::Relaxed) {
            return;
        }
        match solver.solve(&[], slice_conflicts) {
            SolveResult::Sat(model) => { let _ = tx.send(SolveResult::Sat(model)); return; }
            SolveResult::Unsat => { let _ = tx.send(SolveResult::Unsat); return; }
            SolveResult::BudgetExceeded => {}
            SolveResult::Unknown => return,
        }
        for (lits, lbd) in solver.drain_learned() {
            shared_db.export(&lits, lbd as u8);
        }
        let new_clauses = shared_db.import_since(&mut watermark);
        if !new_clauses.is_empty() {
            solver.import_clauses(&new_clauses);
        }
    }
}

// ---------------------------------------------------------------------------
// Solver construction with per-thread diversity
// ---------------------------------------------------------------------------

fn build_diverse_solver(
    num_vars: u32,
    clauses: &[Vec<Literal>],
    thread_id: usize,
) -> CdclSolver {
    let mut solver = CdclSolver::new(num_vars);

    // Load original problem clauses.
    for clause in clauses {
        solver.add_clause(clause);
    }

    // BVE is expensive and identical for every thread — skip it on all but
    // thread 0 which runs the preprocessing pass once.
    // (Thread 0 runs BVE on its first solve() call via the bve_done flag.)
    if thread_id > 0 {
        solver.skip_bve();
    }

    // Polarity bias: even threads prefer TRUE (optimistic), odd prefer FALSE.
    solver.set_polarity_bias(thread_id % 2 == 0);

    // Stagger Luby restart scales so threads don't all restart simultaneously.
    // Base scale 25, then 29, 33, 37 … (step +4 per thread).
    let luby_scale = 25u64.saturating_add(thread_id as u64 * 4);
    solver.set_luby_scale(luby_scale);

    solver
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn par_solve(dimacs: &str, n_threads: usize) -> SolveResult {
        let cnf = crate::parse_dimacs(dimacs).expect("parse error");
        let config = ParallelConfig {
            num_threads: n_threads,
            ..Default::default()
        };
        ParallelCdclSolver::from_dimacs(cnf.num_vars, &cnf.clauses, config).solve()
    }

    #[test]
    fn parallel_trivial_sat() {
        // p cnf 1 1 / clause: [1]
        let result = par_solve("p cnf 1 1\n1 0\n", 2);
        assert!(matches!(result, SolveResult::Sat(_)));
    }

    #[test]
    fn parallel_trivial_unsat() {
        // p cnf 1 2 / [1] and [-1]
        let result = par_solve("p cnf 1 2\n1 0\n-1 0\n", 2);
        assert!(matches!(result, SolveResult::Unsat));
    }

    #[test]
    fn parallel_small_sat() {
        // 3-SAT: (1 ∨ 2) ∧ (¬1 ∨ 3) ∧ (¬2 ∨ ¬3)
        let result = par_solve("p cnf 3 3\n1 2 0\n-1 3 0\n-2 -3 0\n", 4);
        assert!(matches!(result, SolveResult::Sat(_)));
    }

    #[test]
    fn parallel_small_unsat() {
        // Pigeonhole(2,2): encode 3 pigeons into 2 holes
        // Variables x_ij: pigeon i in hole j. i∈{1,2,3}, j∈{1,2}.
        // p11=1,p12=2,p21=3,p22=4,p31=5,p32=6
        // Each pigeon in ≥1 hole: [1,2],[3,4],[5,6]
        // ≤1 pigeon per hole (for each pair of pigeons, not both in same hole):
        // hole 1: [-1,-3],[-1,-5],[-3,-5]
        // hole 2: [-2,-4],[-2,-6],[-4,-6]
        let dimacs = "p cnf 6 9\n\
            1 2 0\n3 4 0\n5 6 0\n\
            -1 -3 0\n-1 -5 0\n-3 -5 0\n\
            -2 -4 0\n-2 -6 0\n-4 -6 0\n";
        let result = par_solve(dimacs, 4);
        assert!(matches!(result, SolveResult::Unsat));
    }

    #[test]
    fn shared_db_export_import() {
        let db = SharedClauseDb::new(6, 1000);
        let lits = vec![Literal::positive(1), Literal::negative(2)];
        db.export(&lits, 2);
        assert_eq!(db.len(), 1);

        let mut wm = 0;
        let imported = db.import_since(&mut wm);
        assert_eq!(imported.len(), 1);
        assert_eq!(wm, 1);

        // Second import from same watermark: nothing new.
        let imported2 = db.import_since(&mut wm);
        assert!(imported2.is_empty());
    }

    #[test]
    fn shared_db_lbd_filter() {
        let db = SharedClauseDb::new(4, 1000);
        let lits = vec![Literal::positive(1)];
        db.export(&lits, 5); // LBD 5 > threshold 4: dropped
        assert_eq!(db.len(), 0);
        db.export(&lits, 4); // LBD 4 == threshold: accepted
        assert_eq!(db.len(), 1);
    }

    #[test]
    fn shared_db_eviction() {
        let db = SharedClauseDb::new(6, 4);
        let lits = vec![Literal::positive(1)];
        for _ in 0..4 { db.export(&lits, 1); }
        assert_eq!(db.len(), 4);
        // Inserting a 5th triggers eviction of 25% = 1 entry.
        db.export(&lits, 1);
        assert_eq!(db.len(), 4); // evicted 1, added 1 → still 4
    }
}
