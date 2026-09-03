//! Axum route handlers.
//!
//! ## Endpoints
//!
//! **Client-facing**
//! - `POST /v1/batch`               — submit proof-farm batch
//! - `GET  /v1/batch/:job_id`       — poll batch results
//! - `POST /v1/cube`                — submit cube-and-conquer job
//! - `GET  /v1/cube/:job_id`        — poll cube verdict
//!
//! **Worker-facing**
//! - `GET  /v1/work`                — long-poll for a task (blocks up to 30 s)
//! - `POST /v1/work/:task_id/result`— report SAT/UNSAT/UNKNOWN or a cube split
//! - `POST /v1/work/:task_id/renew` — extend lease TTL
//! - `POST /v1/heartbeat`           — worker liveness ping
//!
//! **Admin**
//! - `GET  /v1/status`              — coordinator stats

use crate::server::AppState;
use axum::{
    extract::{Path, Query, State},
    http::StatusCode,
    response::IntoResponse,
    Json,
};
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};
use uuid::Uuid;

// ── Request / response types ─────────────────────────────────────────────────

#[derive(Deserialize)]
pub struct BatchRequest {
    pub scripts:       Vec<String>,
    #[serde(default)]
    pub max_conflicts: u64,
}

#[derive(Deserialize)]
pub struct CubeRequest {
    pub script:                   String,
    #[serde(default)]
    pub max_conflicts_per_cube:   u64,
}

#[derive(Deserialize)]
pub struct WorkQuery {
    pub worker_id:      u32,
    #[serde(default = "default_long_poll_ms")]
    pub long_poll_ms:   u64,
}
fn default_long_poll_ms() -> u64 { 30_000 }

#[derive(Serialize)]
pub struct WorkResponse {
    pub task_id:       String,
    pub script:        String,
    pub max_conflicts: u64,
    pub lease_ttl_ms:  u64,
}

#[derive(Deserialize)]
pub struct ResultRequest {
    pub worker_id: u32,
    pub code:      u32,
    #[serde(default)]
    pub model:     String,
    /// Cube split: list of new SMT-LIB 2 `(assert ...)` lines, one per branch.
    pub split:     Option<Vec<String>>,
}

#[derive(Deserialize)]
pub struct RenewRequest {
    pub worker_id: u32,
}

#[derive(Deserialize)]
pub struct HeartbeatRequest {
    pub worker_id: u32,
}

// ── Error helper ──────────────────────────────────────────────────────────────

pub struct ApiError(StatusCode, String);

impl IntoResponse for ApiError {
    fn into_response(self) -> axum::response::Response {
        (self.0, self.1).into_response()
    }
}

fn not_found(msg: impl Into<String>) -> ApiError {
    ApiError(StatusCode::NOT_FOUND, msg.into())
}
fn bad_request(msg: impl Into<String>) -> ApiError {
    ApiError(StatusCode::BAD_REQUEST, msg.into())
}

// ── Client handlers ───────────────────────────────────────────────────────────

pub async fn submit_batch(
    State(app): State<AppState>,
    Json(body): Json<BatchRequest>,
) -> impl IntoResponse {
    let (job_id, count) = {
        let mut s = app.state.lock();
        s.submit_batch(body.scripts, body.max_conflicts)
    };
    if count > 0 {
        app.work_queue.add_permits(count);
    }
    Json(serde_json::json!({ "job_id": job_id }))
}

pub async fn get_batch(
    State(app): State<AppState>,
    Path(job_id): Path<Uuid>,
) -> Result<impl IntoResponse, ApiError> {
    let s = app.state.lock();
    let job = s.batch_jobs.get(&job_id).ok_or_else(|| not_found(format!("batch job {job_id}")))?;
    let results: Vec<serde_json::Value> = job.results.iter().map(|r| match r {
        None    => serde_json::json!({ "status": "pending" }),
        Some(r) => serde_json::json!({ "code": r.code, "model": r.model }),
    }).collect();
    Ok(Json(serde_json::json!({
        "status":  format!("{:?}", job.status).to_lowercase(),
        "pending": job.pending,
        "results": results,
    })))
}

pub async fn submit_cube(
    State(app): State<AppState>,
    Json(body): Json<CubeRequest>,
) -> impl IntoResponse {
    let (job_id, count) = {
        let mut s = app.state.lock();
        s.submit_cube(body.script, body.max_conflicts_per_cube)
    };
    app.work_queue.add_permits(count);
    Json(serde_json::json!({ "job_id": job_id }))
}

pub async fn get_cube(
    State(app): State<AppState>,
    Path(job_id): Path<Uuid>,
) -> Result<impl IntoResponse, ApiError> {
    let s = app.state.lock();
    let job = s.cube_jobs.get(&job_id).ok_or_else(|| not_found(format!("cube job {job_id}")))?;
    let verdict = job.verdict.map(|v| format!("{v:?}").to_lowercase())
                             .unwrap_or_else(|| "unknown".into());
    Ok(Json(serde_json::json!({
        "status":  format!("{:?}", job.status).to_lowercase(),
        "verdict": verdict,
        "nodes":   job.nodes.len(),
    })))
}

// ── Worker handlers ───────────────────────────────────────────────────────────

/// Long-poll for a task. Blocks up to `long_poll_ms` milliseconds.
/// Returns 200 + task JSON, or 204 if nothing is available within the window.
pub async fn get_work(
    State(app): State<AppState>,
    Query(q): Query<WorkQuery>,
) -> axum::response::Response {
    let timeout  = Duration::from_millis(q.long_poll_ms);
    let deadline = tokio::time::Instant::now() + timeout;
    let lease_ttl_ms = {
        let s = app.state.lock();
        s.lease_ttl.as_millis() as u64
    };

    loop {
        // Try to acquire a permit (= one task available in queue).
        let remaining = deadline.saturating_duration_since(tokio::time::Instant::now());
        if remaining.is_zero() {
            return StatusCode::NO_CONTENT.into_response();
        }

        let acquired = tokio::time::timeout(
            remaining,
            app.work_queue.acquire(),
        ).await;

        match acquired {
            Err(_timeout) => return StatusCode::NO_CONTENT.into_response(),
            Ok(Ok(permit)) => {
                // Permit represents one task in queue. Consume it.
                permit.forget();
                let task = {
                    let mut s = app.state.lock();
                    s.pop_task(q.worker_id, Instant::now())
                };
                match task {
                    Some(t) => {
                        let resp = WorkResponse {
                            task_id:       t.id.to_string(),
                            script:        t.script().to_owned(),
                            max_conflicts: t.max_conflicts(),
                            lease_ttl_ms,
                        };
                        return (StatusCode::OK, Json(resp)).into_response();
                    }
                    None => {
                        // Permit acquired but queue empty: shouldn't happen; log and retry.
                        log::warn!("semaphore permit acquired but task queue was empty");
                        continue;
                    }
                }
            }
            Ok(Err(_closed)) => return StatusCode::SERVICE_UNAVAILABLE.into_response(),
        }
    }
}

pub async fn post_result(
    State(app): State<AppState>,
    Path(task_id): Path<Uuid>,
    Json(body): Json<ResultRequest>,
) -> Result<impl IntoResponse, ApiError> {
    let (_, new_tasks) = {
        let mut s = app.state.lock();
        s.report_result(
            task_id,
            body.worker_id,
            body.code,
            body.model,
            body.split,
            Instant::now(),
        ).map_err(|e| bad_request(e))?
    };
    if new_tasks > 0 {
        app.work_queue.add_permits(new_tasks);
    }
    Ok(Json(serde_json::json!({ "ok": true })))
}

pub async fn renew_lease(
    State(app): State<AppState>,
    Path(task_id): Path<Uuid>,
    Json(body): Json<RenewRequest>,
) -> Result<impl IntoResponse, ApiError> {
    let mut s = app.state.lock();
    s.renew_lease(task_id, body.worker_id, Instant::now())
        .map_err(|e| bad_request(e))?;
    Ok(Json(serde_json::json!({ "ok": true })))
}

pub async fn heartbeat(
    State(app): State<AppState>,
    Json(body): Json<HeartbeatRequest>,
) -> impl IntoResponse {
    let mut s = app.state.lock();
    s.touch_worker(body.worker_id, Instant::now());
    Json(serde_json::json!({ "ok": true }))
}

pub async fn status(State(app): State<AppState>) -> impl IntoResponse {
    let s = app.state.lock();
    Json(s.stats())
}
