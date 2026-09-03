//! rm-coordinator — ReasonMesh distributed coordinator.
//!
//! Exposes an HTTP work queue that serves two regimes:
//!
//! ## Regime B — Proof farm (independent subgoals)
//!
//! Submit an array of SMT-LIB 2 scripts; each becomes one task dispatched to
//! whatever worker picks it up first.  The Lean tactic `rm_decide_all` and
//! `RmPool.solveAll` route to this endpoint when operating over a cluster.
//!
//! ```text
//! POST /v1/batch  { scripts: [...], max_conflicts: 0 }
//! → { job_id }
//! GET  /v1/batch/:id
//! → { status: "complete", results: [{code, model}, ...] }
//! ```
//!
//! ## Regime A — Cube-and-conquer (one hard problem)
//!
//! Submit a single SMT-LIB 2 script.  The root is dispatched to one worker.
//! Workers may report a *split*: a list of new `(assert ...)` clauses, one per
//! branch.  The coordinator creates child nodes, each with the parent's cube
//! extended by one branch assertion, and dispatches them as new tasks.
//!
//! ```text
//! POST /v1/cube  { script: "...", max_conflicts_per_cube: 5000 }
//! → { job_id }
//! GET  /v1/cube/:id
//! → { status: "complete", verdict: "unsat", nodes: 1023 }
//! ```
//!
//! ## Workers
//!
//! Workers long-poll `GET /v1/work?worker_id=N&long_poll_ms=30000`.
//! On receiving a task they run the script and POST to `/v1/work/:id/result`.
//! They must renew their lease via `/v1/work/:id/renew` every `lease_ttl / 2`
//! seconds or the task will be re-queued automatically.

pub mod job;
pub mod routes;
pub mod server;
pub mod state;

pub use server::{start_server, AppState, CoordinatorConfig};
