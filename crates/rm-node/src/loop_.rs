//! Core worker loops: heartbeat, task polling, solving, and result reporting.

use crate::Args;
use reqwest::StatusCode;
use serde::Deserialize;
use std::time::Duration;

// ── Wire types ────────────────────────────────────────────────────────────────

/// Response from `GET /v1/work`.
#[derive(Debug, Deserialize)]
pub struct WorkItem {
    pub task_id:       String,
    pub script:        String,
    pub max_conflicts: u64,
    pub lease_ttl_ms:  u64,
}

// ── Heartbeat ─────────────────────────────────────────────────────────────────

/// Pings `/v1/heartbeat` every 15 seconds, forever. Errors are logged and
/// retried — a missed heartbeat is non-fatal (coordinator TTL is 60 s).
pub async fn heartbeat_loop(
    client:    reqwest::Client,
    coord:     String,
    worker_id: u32,
    retry:     Duration,
) {
    let url  = format!("{coord}/v1/heartbeat");
    let body = serde_json::json!({ "worker_id": worker_id });
    loop {
        match client.post(&url).json(&body).send().await {
            Ok(r) if r.status().is_success() => {}
            Ok(r) => log::warn!("heartbeat: coordinator returned {}", r.status()),
            Err(e) => log::warn!("heartbeat: {e}"),
        }
        tokio::time::sleep(Duration::from_secs(15)).await;
        let _ = retry; // retry_ms is used in solve_loop for connection failures
    }
}

// ── Solve loop ────────────────────────────────────────────────────────────────

/// Runs forever: poll for a task → solve on a blocking thread → report result.
/// A single invocation of this function represents one concurrency slot.
pub async fn solve_loop(client: reqwest::Client, args: Args, worker_id: u32) {
    let work_url   = format!("{}/v1/work", args.coordinator);
    let retry      = Duration::from_millis(args.retry_ms);

    loop {
        // ── Step 1: long-poll for a task ──────────────────────────────────────
        let resp = match client
            .get(&work_url)
            .query(&[
                ("worker_id",    worker_id.to_string()),
                ("long_poll_ms", args.long_poll_ms.to_string()),
            ])
            .send()
            .await
        {
            Ok(r)  => r,
            Err(e) => {
                log::warn!("GET /v1/work: {e}; retrying in {retry:?}");
                tokio::time::sleep(retry).await;
                continue;
            }
        };

        match resp.status() {
            StatusCode::NO_CONTENT => {
                // Coordinator had no work within the poll window; loop immediately.
                continue;
            }
            s if !s.is_success() => {
                log::warn!("GET /v1/work: unexpected status {s}");
                tokio::time::sleep(retry).await;
                continue;
            }
            _ => {}
        }

        let item: WorkItem = match resp.json().await {
            Ok(w)  => w,
            Err(e) => {
                log::warn!("parse work response: {e}");
                continue;
            }
        };

        log::info!(
            "task {} received: {} chars, budget={}",
            item.task_id, item.script.len(), item.max_conflicts,
        );

        // ── Step 2: lease renewal (concurrent with solving) ───────────────────
        let renew_handle = {
            let client     = client.clone();
            let coord      = args.coordinator.clone();
            let task_id    = item.task_id.clone();
            let interval   = Duration::from_millis((item.lease_ttl_ms / 2).max(5_000));
            tokio::spawn(async move {
                let url  = format!("{coord}/v1/work/{task_id}/renew");
                let body = serde_json::json!({ "worker_id": worker_id });
                loop {
                    tokio::time::sleep(interval).await;
                    match client.post(&url).json(&body).send().await {
                        Ok(r) if r.status().is_success() => {
                            log::debug!("lease renewed for task {task_id}");
                        }
                        Ok(r) => log::warn!("lease renew {task_id}: {}", r.status()),
                        Err(e) => log::warn!("lease renew {task_id}: {e}"),
                    }
                }
            })
        };

        // ── Step 3: solve on a blocking thread ────────────────────────────────
        let script        = item.script.clone();
        let max_conflicts = item.max_conflicts;

        let solve_result = tokio::task::spawn_blocking(move || {
            solve_script(&script, max_conflicts)
        })
        .await;

        renew_handle.abort();

        let (code, model) = match solve_result {
            Ok(r)  => r,
            Err(e) => {
                log::error!("solver thread panicked for task {}: {e}", item.task_id);
                (2u32, String::new())
            }
        };

        log::info!("task {} → code={code} (0=SAT 1=UNSAT 2=UNKNOWN)", item.task_id);

        // ── Step 4: report result ─────────────────────────────────────────────
        let result_url = format!("{}/v1/work/{}/result", args.coordinator, item.task_id);
        let result_body = serde_json::json!({
            "worker_id": worker_id,
            "code":      code,
            "model":     model,
            "split":     null,
        });

        match client.post(&result_url).json(&result_body).send().await {
            Ok(r) if r.status().is_success() => {
                log::debug!("task {} result accepted", item.task_id);
            }
            Ok(r) => log::warn!("POST result for {}: {}", item.task_id, r.status()),
            Err(e) => log::warn!("POST result for {}: {e}", item.task_id),
        }
    }
}

// ── Solver bridge ─────────────────────────────────────────────────────────────

/// Call `SmtSolver` synchronously. Returns `(code, model_string)`.
/// code: 0=SAT, 1=UNSAT, 2=UNKNOWN
///
/// This runs on a `spawn_blocking` thread so it may block freely.
fn solve_script(script: &str, max_conflicts: u64) -> (u32, String) {
    use rm_smt::{SmtError, SmtStatus};

    let solver = match rm_smt::SmtSolver::parse(script) {
        Ok(s)  => s,
        Err(e) => {
            log::warn!("parse error: {e}");
            return (2, format!("parse error: {e}"));
        }
    };

    match solver.solve(max_conflicts) {
        Err(SmtError::EmptyProblem) => {
            // Empty assertions → trivially satisfiable.
            (0, String::new())
        }
        Err(e) => {
            log::warn!("solver error: {e}");
            (2, format!("solver error: {e}"))
        }
        Ok(r) => match r.status {
            SmtStatus::Unsat => (1, String::new()),
            SmtStatus::Sat   => {
                let model = r.values.iter()
                    .map(|(name, val)| format!("({name} {val})"))
                    .collect::<Vec<_>>()
                    .join(" ");
                (0, model)
            }
            SmtStatus::Unknown => (2, String::new()),
        },
    }
}

// ── Unit tests ────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn solve_bv_unsat() {
        let script =
            "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 4))\n\
             (assert (= x #b0000))\n\
             (assert (= x #b1111))\n\
             (check-sat)\n";
        let (code, _) = solve_script(script, 10_000);
        assert_eq!(code, 1);
    }

    #[test]
    fn solve_bv_sat() {
        let script =
            "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 8))\n\
             (assert (bvult x (_ bv10 8)))\n\
             (check-sat)\n";
        let (code, model) = solve_script(script, 10_000);
        assert_eq!(code, 0);
        assert!(!model.is_empty(), "expected model string");
    }

    #[test]
    fn solve_idl_unsat() {
        let script =
            "(set-logic QF_IDL)\n\
             (declare-const x Int)\n\
             (declare-const y Int)\n\
             (assert (<= (- x y) 1))\n\
             (assert (<= (- y x) -3))\n\
             (check-sat)\n";
        let (code, _) = solve_script(script, 10_000);
        assert_eq!(code, 1);
    }

    #[test]
    fn solve_parse_error_returns_unknown() {
        let (code, msg) = solve_script("((((", 100);
        assert_eq!(code, 2);
        assert!(msg.contains("parse error"));
    }

    #[test]
    fn solve_empty_problem_returns_sat() {
        // Empty assertions → EmptyProblem from solver → we treat as trivially SAT.
        let (code, _) = solve_script("(set-logic QF_BV)", 100);
        assert_eq!(code, 0);
    }
}
