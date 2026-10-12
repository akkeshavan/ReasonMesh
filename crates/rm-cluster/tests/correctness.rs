//! Differential correctness tests for parallel CDCL and cluster transport.
//!
//! Strategy:
//!   1. Run each instance through single-threaded CdclSolver → ground truth.
//!   2. Run the same instance through ParallelCdclSolver with 1, 2, 4, 8 workers.
//!   3. Run the same instance through the TCP cluster (coordinator + 1/2 workers,
//!      1 and 2 cubes).
//!   4. Assert all modes return the same SAT/UNSAT verdict.
//!   5. For SAT results, verify the returned model satisfies every clause.

use std::net::SocketAddr;

use rm_sat::{parse_dimacs, DimacsCnf, Model, ParallelCdclSolver, ParallelConfig, SolveResult};
use rm_cluster::{ClusterCoordinator, ClusterResult, ClusterWorkerNode};

// ---------------------------------------------------------------------------
// Test corpus
// ---------------------------------------------------------------------------

/// A DIMACS instance with a known verdict.
struct Instance {
    name: &'static str,
    dimacs: &'static str,
    expected_sat: bool,
}

/// Embed a variety of known instances so the test has no file-system dependency.
fn corpus() -> Vec<Instance> {
    vec![
        // ---- trivially SAT ----
        Instance {
            name: "unit_sat",
            dimacs: "p cnf 1 1\n1 0\n",
            expected_sat: true,
        },
        Instance {
            name: "two_vars_sat",
            dimacs: "p cnf 2 2\n1 2 0\n-1 -2 0\n",
            expected_sat: true,
        },
        // ---- trivially UNSAT ----
        Instance {
            name: "unit_unsat",
            dimacs: "p cnf 1 2\n1 0\n-1 0\n",
            expected_sat: false,
        },
        Instance {
            name: "two_var_unsat",
            // All 4 resolvents of 2 variables — covers every truth table row → UNSAT
            dimacs: "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n",
            expected_sat: false,
        },
        // ---- Pigeonhole PHP(3,2): 3 pigeons in 2 holes → UNSAT ----
        Instance {
            name: "php_3_2_unsat",
            // Variables: x_{i,j} = pigeon i in hole j (i=1..3, j=1..2)
            //   x11=1, x12=2, x21=3, x22=4, x31=5, x32=6
            // Each pigeon in at least one hole:
            //   (x11 | x12), (x21 | x22), (x31 | x32)
            // No two pigeons in same hole:
            //   (-x11 | -x21), (-x11 | -x31), (-x21 | -x31),
            //   (-x12 | -x22), (-x12 | -x32), (-x22 | -x32)
            dimacs: "p cnf 6 9\n\
                     1 2 0\n3 4 0\n5 6 0\n\
                     -1 -3 0\n-1 -5 0\n-3 -5 0\n\
                     -2 -4 0\n-2 -6 0\n-4 -6 0\n",
            expected_sat: false,
        },
        // ---- PHP(3,3): 3 pigeons in 3 holes → SAT ----
        Instance {
            name: "php_3_3_sat",
            // x11..x33 (9 vars). Each pigeon in at least one hole;
            // no two pigeons in same hole. Solution: pigeon i → hole i.
            dimacs: "p cnf 9 12\n\
                     1 2 3 0\n4 5 6 0\n7 8 9 0\n\
                     -1 -4 0\n-1 -7 0\n-4 -7 0\n\
                     -2 -5 0\n-2 -8 0\n-5 -8 0\n\
                     -3 -6 0\n-3 -9 0\n-6 -9 0\n",
            expected_sat: true,
        },
        // ---- Random 3-SAT (seeded, known sat) ----
        // Generated offline with n=20, m=80 (ratio 4.0 < 4.27 → likely SAT).
        Instance {
            name: "r3sat_20_80_sat",
            dimacs: "p cnf 20 80\n\
                2 -8 14 0\n-1 5 -12 0\n3 -7 15 0\n-4 10 -16 0\n6 -9 18 0\n\
                -11 13 -17 0\n1 -6 19 0\n-2 7 -18 0\n4 -10 20 0\n-3 8 -14 0\n\
                5 -11 16 0\n-6 9 -13 0\n2 -15 17 0\n-1 12 -19 0\n3 -8 20 0\n\
                -4 7 -16 0\n5 -9 14 0\n-2 10 -18 0\n1 -13 17 0\n-3 6 -20 0\n\
                4 -11 15 0\n-5 8 -19 0\n2 -7 16 0\n-1 9 -14 0\n3 -10 18 0\n\
                -4 12 -17 0\n5 -6 19 0\n-2 11 -15 0\n1 -8 13 0\n-3 7 -20 0\n\
                6 -12 14 0\n-1 10 -16 0\n2 -9 18 0\n-5 11 -17 0\n3 -13 19 0\n\
                -4 8 -15 0\n6 -7 20 0\n-2 12 -14 0\n1 -10 16 0\n-3 9 -18 0\n\
                5 -11 17 0\n-6 13 -19 0\n2 -8 15 0\n-1 7 -20 0\n4 -12 14 0\n\
                -5 10 -16 0\n3 -9 18 0\n-2 11 -17 0\n6 -8 19 0\n-1 12 -15 0\n\
                4 -7 13 0\n-3 10 -20 0\n5 -11 16 0\n-6 8 -14 0\n2 -9 17 0\n\
                -1 13 -19 0\n3 -8 15 0\n-4 7 -16 0\n6 -10 20 0\n-2 11 -18 0\n\
                1 -12 17 0\n-5 9 -14 0\n3 -7 19 0\n-4 10 -15 0\n2 -11 16 0\n\
                -1 8 -20 0\n5 -9 18 0\n-6 12 -17 0\n4 -13 19 0\n-2 7 -15 0\n\
                1 -10 16 0\n-3 11 -20 0\n6 -8 14 0\n-5 9 -17 0\n2 -12 18 0\n\
                -1 13 -19 0\n4 -7 15 0\n-3 10 -16 0\n5 -11 20 0\n-2 8 -14 0\n",
            expected_sat: true,
        },
        // ---- PHP(4,3): 4 pigeons in 3 holes → UNSAT ----
        Instance {
            name: "php_4_3_unsat",
            // x_{i,j} = pigeon i in hole j; var = 3*(i-1)+j  (1-indexed)
            // p1: 1,2,3  p2: 4,5,6  p3: 7,8,9  p4: 10,11,12
            // At-least-one per pigeon (4) + at-most-one per hole (3×C(4,2)=18) = 22 clauses
            dimacs: "p cnf 12 22\n\
                     1 2 3 0\n4 5 6 0\n7 8 9 0\n10 11 12 0\n\
                     -1 -4 0\n-1 -7 0\n-1 -10 0\n-4 -7 0\n-4 -10 0\n-7 -10 0\n\
                     -2 -5 0\n-2 -8 0\n-2 -11 0\n-5 -8 0\n-5 -11 0\n-8 -11 0\n\
                     -3 -6 0\n-3 -9 0\n-3 -12 0\n-6 -9 0\n-6 -12 0\n-9 -12 0\n",
            expected_sat: false,
        },
        // ---- Random 3-SAT (n=30, m=127, ratio≈4.23 → near threshold, SAT) ----
        Instance {
            name: "r3sat_30_127_sat",
            dimacs: "p cnf 30 127\n\
                1 -8 22 0\n-2 15 -27 0\n3 -11 25 0\n-4 18 -23 0\n5 -12 30 0\n\
                -6 19 -26 0\n7 -9 21 0\n-1 14 -28 0\n2 -16 24 0\n-3 10 -29 0\n\
                4 -13 27 0\n-5 17 -22 0\n6 -11 28 0\n-7 15 -23 0\n1 -18 26 0\n\
                -2 12 -30 0\n3 -19 24 0\n-4 9 -25 0\n5 -14 29 0\n-6 16 -21 0\n\
                7 -10 23 0\n-1 13 -27 0\n2 -17 22 0\n-3 20 -28 0\n4 -8 25 0\n\
                -5 11 -30 0\n6 -15 26 0\n-7 12 -24 0\n1 -19 29 0\n-2 16 -23 0\n\
                3 -14 21 0\n-4 18 -27 0\n5 -9 28 0\n-6 13 -22 0\n7 -17 25 0\n\
                -1 20 -30 0\n2 -10 24 0\n-3 15 -26 0\n4 -11 29 0\n-5 19 -23 0\n\
                6 -8 21 0\n-7 14 -27 0\n1 -16 25 0\n-2 12 -28 0\n3 -18 22 0\n\
                -4 20 -26 0\n5 -13 30 0\n-6 9 -24 0\n7 -17 23 0\n-1 11 -29 0\n\
                2 -15 27 0\n-3 19 -21 0\n4 -10 28 0\n-5 16 -22 0\n6 -14 25 0\n\
                -7 18 -30 0\n1 -12 24 0\n-2 20 -26 0\n3 -8 29 0\n-4 13 -23 0\n\
                5 -17 21 0\n-6 15 -27 0\n7 -11 22 0\n-1 19 -25 0\n2 -9 28 0\n\
                -3 16 -30 0\n4 -14 26 0\n-5 10 -23 0\n6 -18 29 0\n-7 12 -24 0\n\
                1 -20 21 0\n-2 13 -27 0\n3 -17 25 0\n-4 15 -22 0\n5 -11 28 0\n\
                -6 19 -30 0\n7 -9 24 0\n-1 16 -26 0\n2 -14 23 0\n-3 18 -29 0\n\
                4 -12 21 0\n-5 20 -27 0\n6 -10 25 0\n-7 13 -22 0\n1 -17 28 0\n\
                -2 11 -30 0\n3 -15 26 0\n-4 19 -24 0\n5 -8 23 0\n-6 14 -29 0\n\
                7 -16 21 0\n-1 12 -25 0\n2 -18 27 0\n-3 20 -22 0\n4 -9 28 0\n\
                -5 13 -30 0\n6 -17 26 0\n-7 11 -24 0\n1 -19 22 0\n-2 15 -29 0\n\
                3 -10 25 0\n-4 16 -23 0\n5 -14 27 0\n-6 12 -21 0\n7 -18 30 0\n\
                -1 20 -26 0\n2 -8 24 0\n-3 13 -28 0\n4 -17 22 0\n-5 19 -25 0\n\
                6 -11 29 0\n-7 15 -23 0\n1 -10 21 0\n-2 18 -27 0\n3 -16 30 0\n\
                -4 14 -24 0\n5 -9 26 0\n-6 20 -22 0\n7 -12 28 0\n-1 17 -25 0\n\
                2 -19 23 0\n-3 11 -29 0\n4 -15 21 0\n-5 18 -27 0\n6 -13 30 0\n\
                -7 16 -24 0\n1 -8 26 0\n",
            expected_sat: true,
        },
    ]
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Verdict { Sat, Unsat }

fn verdict(r: &SolveResult) -> Option<Verdict> {
    match r {
        SolveResult::Sat(_) => Some(Verdict::Sat),
        SolveResult::Unsat  => Some(Verdict::Unsat),
        _                   => None,
    }
}

fn check_model(cnf: &DimacsCnf, model: &Model) -> bool {
    model.verify_dimacs(&cnf.clauses)
}

/// Solve `cnf` with single-threaded CDCL.  Used as the correctness oracle.
fn oracle(cnf: &DimacsCnf) -> Verdict {
    let config = ParallelConfig { num_threads: 1, ..Default::default() };
    let solver = ParallelCdclSolver::from_dimacs(cnf.num_vars, &cnf.clauses, config);
    match solver.solve() {
        SolveResult::Sat(_) => Verdict::Sat,
        SolveResult::Unsat  => Verdict::Unsat,
        other => panic!("oracle returned {other:?}"),
    }
}

/// Generate N exhaustive cubes by fixing the first ceil(log2(N)) variables.
fn make_cubes(n: u32, num_vars: u32) -> Vec<Vec<i32>> {
    if n <= 1 || num_vars == 0 {
        return vec![vec![]];
    }
    let k = (n as f64).log2().ceil() as u32;
    let k = k.min(num_vars);
    (0..(1u32 << k))
        .map(|mask| {
            (0..k).map(|bit| {
                let var = (bit + 1) as i32;
                if mask & (1 << bit) != 0 { var } else { -var }
            }).collect()
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Cross-mode checks
// ---------------------------------------------------------------------------

fn check_parallel(cnf: &DimacsCnf, expected: Verdict, n_threads: usize) {
    let config = ParallelConfig {
        num_threads: n_threads,
        ..Default::default()
    };
    let solver = ParallelCdclSolver::from_dimacs(cnf.num_vars, &cnf.clauses, config);
    let result = solver.solve();

    let v = verdict(&result).unwrap_or_else(|| panic!("parallel({n_threads}) returned Unknown"));
    assert_eq!(
        v, expected,
        "parallel({n_threads} threads) disagrees with oracle: got {v:?}, want {expected:?}"
    );

    if let SolveResult::Sat(model) = &result {
        assert!(
            check_model(cnf, model),
            "parallel({n_threads}) returned SAT but model is invalid"
        );
    }
}

async fn check_cluster(cnf: &DimacsCnf, expected: Verdict, n_workers: usize, n_cubes: u32) {
    let cubes = make_cubes(n_cubes, cnf.num_vars);
    let coord = ClusterCoordinator;
    let bound = coord.bind("127.0.0.1:0".parse::<SocketAddr>().unwrap()).await.unwrap();
    let addr  = bound.addr;

    for _ in 0..n_workers {
        tokio::spawn(async move {
            ClusterWorkerNode::new(1).run(addr).await.ok();
        });
    }

    let result = bound.run(cnf.num_vars, cnf.clauses.clone(), cubes).await;
    let v = match &result {
        ClusterResult::Sat   => Verdict::Sat,
        ClusterResult::Unsat => Verdict::Unsat,
        ClusterResult::Failed(e) => panic!("cluster failed: {e}"),
    };
    assert_eq!(
        v, expected,
        "cluster({n_workers}w,{n_cubes}c) disagrees with oracle: got {v:?}, want {expected:?}"
    );
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// Verify every corpus instance against the oracle (sanity-check the corpus).
#[test]
fn corpus_oracle_sanity() {
    for inst in corpus() {
        let cnf = parse_dimacs(inst.dimacs).unwrap_or_else(|e| panic!("{}: parse error: {e}", inst.name));
        let v = oracle(&cnf);
        let want = if inst.expected_sat { Verdict::Sat } else { Verdict::Unsat };
        assert_eq!(v, want, "{}: oracle returned {v:?}, expected {want:?}", inst.name);
    }
}

/// Parallel CDCL matches oracle across 1, 2, 4, 8 worker counts.
#[test]
fn parallel_matches_oracle() {
    for inst in corpus() {
        let cnf = parse_dimacs(inst.dimacs).unwrap();
        let expected = oracle(&cnf);
        for &n in &[1usize, 2, 4, 8] {
            check_parallel(&cnf, expected, n);
        }
    }
}

/// Cluster transport matches oracle: 1 worker (sequential), 2 workers, 4 cubes.
#[tokio::test]
async fn cluster_matches_oracle_1_worker() {
    for inst in corpus() {
        let cnf = parse_dimacs(inst.dimacs).unwrap();
        let expected = oracle(&cnf);
        // 1 worker, 1 cube = sequential cluster (just tests transport)
        check_cluster(&cnf, expected, 1, 1).await;
    }
}

#[tokio::test]
async fn cluster_matches_oracle_2_workers_2_cubes() {
    for inst in corpus() {
        let cnf = parse_dimacs(inst.dimacs).unwrap();
        let expected = oracle(&cnf);
        check_cluster(&cnf, expected, 2, 2).await;
    }
}

#[tokio::test]
async fn cluster_matches_oracle_2_workers_4_cubes() {
    for inst in corpus() {
        let cnf = parse_dimacs(inst.dimacs).unwrap();
        let expected = oracle(&cnf);
        // More cubes than workers: workers take turns, serial+parallel mix
        check_cluster(&cnf, expected, 2, 4).await;
    }
}

/// For every SAT result from the parallel solver, the model satisfies all clauses.
#[test]
fn parallel_sat_models_are_valid() {
    for inst in corpus() {
        let cnf = parse_dimacs(inst.dimacs).unwrap();
        for &n in &[1usize, 2, 4] {
            let config = ParallelConfig { num_threads: n, ..Default::default() };
            let result = ParallelCdclSolver::from_dimacs(cnf.num_vars, &cnf.clauses, config).solve();
            if let SolveResult::Sat(model) = &result {
                assert!(
                    check_model(&cnf, model),
                    "{} ({}t): SAT model is invalid",
                    inst.name, n
                );
            }
        }
    }
}

/// Cross-mode agreement: parallel and cluster must agree with each other
/// (both already agree with oracle, but explicit cross-check clarifies intent).
#[tokio::test]
async fn parallel_and_cluster_agree() {
    for inst in corpus() {
        let cnf = parse_dimacs(inst.dimacs).unwrap();
        let par_result = ParallelCdclSolver::from_dimacs(
            cnf.num_vars, &cnf.clauses,
            ParallelConfig { num_threads: 2, ..Default::default() }
        ).solve();
        let par_v = verdict(&par_result).expect("parallel returned Unknown");

        let coord = ClusterCoordinator;
        let bound = coord.bind("127.0.0.1:0".parse::<SocketAddr>().unwrap()).await.unwrap();
        let addr = bound.addr;
        tokio::spawn(async move { ClusterWorkerNode::new(1).run(addr).await.ok(); });
        let clus_v = match bound.run(cnf.num_vars, cnf.clauses.clone(), vec![vec![]]).await {
            ClusterResult::Sat   => Verdict::Sat,
            ClusterResult::Unsat => Verdict::Unsat,
            ClusterResult::Failed(e) => panic!("{}: cluster failed: {e}", inst.name),
        };

        assert_eq!(par_v, clus_v, "{}: parallel={par_v:?} cluster={clus_v:?}", inst.name);
    }
}
