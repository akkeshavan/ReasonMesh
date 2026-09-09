// BCP micro-benchmark: loads a real CNF and runs the solver for a fixed number
// of conflicts, measuring propagation throughput and time spent in each BCP branch.
//
// Run with:
//   cargo bench -p rm-sat --bench bcp -- --nocapture
//
// For profiling with samply:
//   samply record cargo bench -p rm-sat --bench bcp -- --nocapture --profile-time 10

use rm_sat::{parse_dimacs, CdclSolver};
use rm_akx::literal::Literal;
use std::time::Instant;

fn dimacs_lit(l: i32) -> Literal {
    if l > 0 { Literal::positive(l as u32) } else { Literal::negative((-l) as u32) }
}

fn load_and_run(cnf_bytes: &str, conflict_limit: u64) -> (u64, u64, f64) {
    let cnf = parse_dimacs(cnf_bytes).expect("valid dimacs");
    let mut solver = CdclSolver::new(cnf.num_vars);
    for clause in &cnf.clauses {
        let lits: Vec<Literal> = clause.iter().map(|&l| dimacs_lit(l)).collect();
        solver.add_clause(&lits);
    }
    let t0 = Instant::now();
    solver.solve_with_deadline(&[], conflict_limit, None);
    let elapsed = t0.elapsed().as_secs_f64();
    (solver.propagations, solver.conflicts, elapsed)
}

fn main() {
    // Use the two hard random 3-SAT instances that show the gap.
    let problems: &[(&str, &str)] = &[
        ("r3sat-238-2",    include_str!("../../../benchmarks/g2/r3sat-238-2.cnf")),
        ("r3sat-240-r425", include_str!("../../../benchmarks/g2/r3sat-240-r425.cnf")),
    ];

    println!("{:<22} {:>12} {:>12} {:>10} {:>12}", "problem", "props", "conflicts", "secs", "Mprop/s");
    println!("{}", "-".repeat(72));

    for &(name, cnf) in problems {
        // Warm-up run (avoids branch predictor cold start)
        load_and_run(cnf, 5_000);

        // Timed run: cap at 200k conflicts to get stable numbers
        let (props, confs, secs) = load_and_run(cnf, 200_000);
        let mprop_s = props as f64 / secs / 1_000_000.0;
        println!("{:<22} {:>12} {:>12} {:>10.3} {:>12.2}",
            name, props, confs, secs, mprop_s);
    }

    // Second pass: measure BCP branch hit rates by counting per-path visits.
    // We instrument with counters added to the solver itself via a test-only path.
    println!("\n--- BCP branch analysis (first 50k conflicts) ---");
    for &(name, cnf) in problems {
        let cnf_parsed = parse_dimacs(cnf).unwrap();
        let mut solver = CdclSolver::new(cnf_parsed.num_vars);
        for clause in &cnf_parsed.clauses {
            let lits: Vec<Literal> = clause.iter().map(|&l| dimacs_lit(l)).collect();
            solver.add_clause(&lits);
        }
        let t0 = Instant::now();
        solver.solve_with_deadline(&[], 50_000, None);
        let secs = t0.elapsed().as_secs_f64();
        let bcp_stats = solver.bcp_stats();
        println!("\n{name}  ({:.3}s, {} props, {} conflicts):",
            secs, solver.propagations, solver.conflicts);
        println!("  binary_checks:       {:>12}  ({:.1}% of props)",
            bcp_stats.binary_checks,
            100.0 * bcp_stats.binary_checks as f64 / solver.propagations.max(1) as f64);
        println!("  blocker_hits:        {:>12}  ({:.1}% of watch entries visited)",
            bcp_stats.blocker_hits,
            100.0 * bcp_stats.blocker_hits as f64 / bcp_stats.watch_entries_visited.max(1) as f64);
        println!("  clause_fetch:        {:>12}  ({:.1}% of watch entries visited)",
            bcp_stats.clause_fetches,
            100.0 * bcp_stats.clause_fetches as f64 / bcp_stats.watch_entries_visited.max(1) as f64);
        println!("  watch_entries_total: {:>12}", bcp_stats.watch_entries_visited);
        println!("  new_watch_found:     {:>12}  ({:.1}% of clause fetches)",
            bcp_stats.new_watch_found,
            100.0 * bcp_stats.new_watch_found as f64 / bcp_stats.clause_fetches.max(1) as f64);
        println!("  unit_props:          {:>12}  ({:.1}% of clause fetches)",
            bcp_stats.unit_props,
            100.0 * bcp_stats.unit_props as f64 / bcp_stats.clause_fetches.max(1) as f64);
        println!("  conflicts_in_bcp:    {:>12}  ({:.1}% of clause fetches)",
            bcp_stats.bcp_conflicts,
            100.0 * bcp_stats.bcp_conflicts as f64 / bcp_stats.clause_fetches.max(1) as f64);
    }
}
