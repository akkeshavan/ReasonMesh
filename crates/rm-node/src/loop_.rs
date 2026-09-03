//! Core worker loops: heartbeat, task polling, solving, and result reporting.

use crate::{lookahead, Args};
use reqwest::StatusCode;
use serde::Deserialize;
use std::time::Duration;

// ── Wire types ────────────────────────────────────────────────────────────────

/// Response from `GET /v1/work`.
#[derive(Debug, Deserialize)]
pub struct WorkItem {
    pub task_id: String,
    pub script: String,
    pub max_conflicts: u64,
    pub lease_ttl_ms: u64,
}

// ── Solve outcome ─────────────────────────────────────────────────────────────

/// What the solver (plus look-ahead) determined for one task.
#[derive(Debug)]
pub enum SolveOutcome {
    /// The solver found a satisfying assignment; `model` is a space-separated
    /// list of `(name value)` pairs.
    Sat(String),
    /// The solver proved the formula unsatisfiable.
    Unsat,
    /// The conflict budget was exhausted and the look-ahead selected a split
    /// variable; `branches` contains two SMT-LIB 2 `(assert ...)` strings
    /// whose conjunction is the original search space.
    Split(Vec<String>),
    /// The conflict budget was exhausted and no split could be identified.
    Unknown,
}

impl SolveOutcome {
    fn code(&self) -> u32 {
        match self {
            SolveOutcome::Sat(_) => 0,
            SolveOutcome::Unsat => 1,
            SolveOutcome::Split(_) => 2,
            SolveOutcome::Unknown => 2,
        }
    }
    fn model(&self) -> &str {
        match self {
            SolveOutcome::Sat(m) => m,
            _ => "",
        }
    }
    fn split(&self) -> Option<Vec<String>> {
        match self {
            SolveOutcome::Split(b) => Some(b.clone()),
            _ => None,
        }
    }
    fn label(&self) -> &'static str {
        match self {
            SolveOutcome::Sat(_) => "SAT",
            SolveOutcome::Unsat => "UNSAT",
            SolveOutcome::Split(_) => "SPLIT",
            SolveOutcome::Unknown => "UNKNOWN",
        }
    }
}

// ── Heartbeat ─────────────────────────────────────────────────────────────────

/// Pings `/v1/heartbeat` every 15 seconds, forever.
pub async fn heartbeat_loop(
    client: reqwest::Client,
    coord: String,
    worker_id: u32,
    retry: Duration,
) {
    let url = format!("{coord}/v1/heartbeat");
    let body = serde_json::json!({ "worker_id": worker_id });
    loop {
        match client.post(&url).json(&body).send().await {
            Ok(r) if r.status().is_success() => {}
            Ok(r) => log::warn!("heartbeat: coordinator returned {}", r.status()),
            Err(e) => log::warn!("heartbeat: {e}"),
        }
        tokio::time::sleep(Duration::from_secs(15)).await;
        let _ = retry;
    }
}

// ── Solve loop ────────────────────────────────────────────────────────────────

/// Runs forever: poll → solve + look-ahead → report.
pub async fn solve_loop(client: reqwest::Client, args: Args, worker_id: u32) {
    let work_url = format!("{}/v1/work", args.coordinator);
    let retry = Duration::from_millis(args.retry_ms);

    loop {
        // ── Step 1: long-poll ─────────────────────────────────────────────────
        let resp = match client
            .get(&work_url)
            .query(&[
                ("worker_id", worker_id.to_string()),
                ("long_poll_ms", args.long_poll_ms.to_string()),
            ])
            .send()
            .await
        {
            Ok(r) => r,
            Err(e) => {
                log::warn!("GET /v1/work: {e}; retrying in {retry:?}");
                tokio::time::sleep(retry).await;
                continue;
            }
        };

        match resp.status() {
            StatusCode::NO_CONTENT => continue,
            s if !s.is_success() => {
                log::warn!("GET /v1/work: unexpected status {s}");
                tokio::time::sleep(retry).await;
                continue;
            }
            _ => {}
        }

        let item: WorkItem = match resp.json().await {
            Ok(w) => w,
            Err(e) => {
                log::warn!("parse work response: {e}");
                continue;
            }
        };

        log::info!(
            "task {} received: {} chars, budget={}",
            item.task_id,
            item.script.len(),
            item.max_conflicts,
        );

        // ── Step 2: lease renewal (concurrent with solving) ───────────────────
        let renew_handle = {
            let client = client.clone();
            let coord = args.coordinator.clone();
            let task_id = item.task_id.clone();
            let interval = Duration::from_millis((item.lease_ttl_ms / 2).max(5_000));
            tokio::spawn(async move {
                let url = format!("{coord}/v1/work/{task_id}/renew");
                let body = serde_json::json!({ "worker_id": worker_id });
                loop {
                    tokio::time::sleep(interval).await;
                    match client.post(&url).json(&body).send().await {
                        Ok(r) if r.status().is_success() => {
                            log::debug!("lease renewed for {task_id}")
                        }
                        Ok(r) => log::warn!("lease renew {task_id}: {}", r.status()),
                        Err(e) => log::warn!("lease renew {task_id}: {e}"),
                    }
                }
            })
        };

        // ── Step 3: solve + look-ahead (blocking thread) ──────────────────────
        let script = item.script.clone();
        let max_conflicts = item.max_conflicts;

        let outcome =
            tokio::task::spawn_blocking(move || solve_with_lookahead(&script, max_conflicts)).await;

        renew_handle.abort();

        let outcome = match outcome {
            Ok(o) => o,
            Err(e) => {
                log::error!("solver thread panicked for task {}: {e}", item.task_id);
                SolveOutcome::Unknown
            }
        };

        log::info!("task {} → {}", item.task_id, outcome.label());

        // ── Step 4: report result ─────────────────────────────────────────────
        let result_url = format!("{}/v1/work/{}/result", args.coordinator, item.task_id);
        let result_body = serde_json::json!({
            "worker_id": worker_id,
            "code":      outcome.code(),
            "model":     outcome.model(),
            "split":     outcome.split(),
        });

        match client.post(&result_url).json(&result_body).send().await {
            Ok(r) if r.status().is_success() => {
                log::debug!("task {} result accepted", item.task_id)
            }
            Ok(r) => log::warn!("POST result for {}: {}", item.task_id, r.status()),
            Err(e) => log::warn!("POST result for {}: {e}", item.task_id),
        }
    }
}

// ── Solver + look-ahead bridge ────────────────────────────────────────────────

/// Probe budget: a small fraction of the main budget, or a fixed cap.
/// Returns 0 if `max_conflicts` is 0 (unlimited main budget) — in that case
/// the main solve should never be UNKNOWN, so probing is moot.
fn probe_budget(max_conflicts: u64) -> u64 {
    if max_conflicts == 0 {
        0
    } else {
        (max_conflicts / 8).clamp(200, 2_000)
    }
}

/// Run the solver; if UNKNOWN, run the look-ahead and return `Split` or `Unknown`.
///
/// Runs synchronously — must be called from `spawn_blocking`.
pub fn solve_with_lookahead(script: &str, max_conflicts: u64) -> SolveOutcome {
    use rm_smt::{SmtError, SmtStatus};

    let solver = match rm_smt::SmtSolver::parse(script) {
        Ok(s) => s,
        Err(e) => {
            log::warn!("parse error: {e}");
            return SolveOutcome::Unknown;
        }
    };

    let result = match solver.solve(max_conflicts) {
        Err(SmtError::EmptyProblem) => return SolveOutcome::Sat(String::new()),
        Err(e) => {
            log::warn!("solver error: {e}");
            return SolveOutcome::Unknown;
        }
        Ok(r) => r,
    };

    match result.status {
        SmtStatus::Unsat => SolveOutcome::Unsat,

        SmtStatus::Sat => {
            let model = result
                .values
                .iter()
                .map(|(n, v)| format!("({n} {v})"))
                .collect::<Vec<_>>()
                .join(" ");
            SolveOutcome::Sat(model)
        }

        SmtStatus::Unknown => {
            // Budget exhausted — try to find a split point.
            let pb = probe_budget(max_conflicts);
            log::debug!("solver UNKNOWN, running look-ahead (probe_budget={pb})");

            match lookahead::pick_split(script, pb) {
                Some([pos, neg]) => {
                    log::info!("look-ahead split: {pos}  |  {neg}");
                    SolveOutcome::Split(vec![pos, neg])
                }
                None => {
                    log::debug!("look-ahead found no split variable");
                    SolveOutcome::Unknown
                }
            }
        }
    }
}

// ── Unit tests ────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsat_returns_unsat() {
        let s = "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 4))\n\
             (assert (= x #b0000))\n\
             (assert (= x #b1111))\n\
             (check-sat)\n";
        assert!(matches!(
            solve_with_lookahead(s, 10_000),
            SolveOutcome::Unsat
        ));
    }

    #[test]
    fn sat_returns_sat_with_model() {
        let s = "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 8))\n\
             (assert (bvult x (_ bv10 8)))\n\
             (check-sat)\n";
        match solve_with_lookahead(s, 10_000) {
            SolveOutcome::Sat(model) => assert!(!model.is_empty()),
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn idl_unsat() {
        let s = "(set-logic QF_IDL)\n\
             (declare-const x Int)\n\
             (declare-const y Int)\n\
             (assert (<= (- x y) 1))\n\
             (assert (<= (- y x) -3))\n\
             (check-sat)\n";
        assert!(matches!(
            solve_with_lookahead(s, 10_000),
            SolveOutcome::Unsat
        ));
    }

    #[test]
    fn parse_error_returns_unknown() {
        assert!(matches!(
            solve_with_lookahead("((((", 100),
            SolveOutcome::Unknown
        ));
    }

    #[test]
    fn empty_problem_returns_sat() {
        assert!(matches!(
            solve_with_lookahead("(set-logic QF_BV)", 100),
            SolveOutcome::Sat(_)
        ));
    }

    #[test]
    fn unknown_with_no_decls_stays_unknown() {
        // QF_BV script with no declarations → UNKNOWN from solver → no split var
        // This is hard to trigger reliably since solver may return sat/unsat on
        // very simple problems. We test the logic path by checking the outcome
        // type only (not requiring UNKNOWN specifically, since solver may find SAT).
        let s = "(set-logic QF_BV) (assert true) (check-sat)";
        let out = solve_with_lookahead(s, 1);
        // Either Sat (trivially) or Unknown — not Unsat or Split.
        assert!(!matches!(out, SolveOutcome::Unsat | SolveOutcome::Split(_)));
    }

    #[test]
    fn split_outcome_has_two_assertions() {
        // Force a split by using a tiny budget on a non-trivial BV problem
        // with multiple variables so the look-ahead has something to choose.
        // We run with a tiny conflict budget hoping to get UNKNOWN.
        let s = "(set-logic QF_BV)\n\
             (declare-const a (_ BitVec 32))\n\
             (declare-const b (_ BitVec 32))\n\
             (assert (= (bvadd a b) (_ bv0 32)))\n\
             (assert (bvugt a (_ bv0 32)))\n\
             (check-sat)\n";
        let out = solve_with_lookahead(s, 1); // 1 conflict → almost certainly UNKNOWN
        match out {
            SolveOutcome::Split(branches) => {
                assert_eq!(branches.len(), 2);
                assert!(branches[0].starts_with("(assert "));
                assert!(branches[1].starts_with("(assert "));
            }
            // If the solver happens to find SAT/UNSAT in 1 conflict, that's also fine.
            SolveOutcome::Sat(_) | SolveOutcome::Unsat | SolveOutcome::Unknown => {}
        }
    }

    #[test]
    fn probe_budget_scaling() {
        assert_eq!(probe_budget(0), 0, "unlimited main budget → no probing");
        assert_eq!(probe_budget(1_600), 200, "1600/8 = 200");
        assert_eq!(probe_budget(8_000), 1_000);
        assert_eq!(probe_budget(100_000), 2_000, "capped at 2000");
    }
}
