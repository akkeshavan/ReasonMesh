//! Server startup, background maintenance tasks, and `AppState`.

use crate::routes;
use crate::state::CoordinatorState;
use axum::{
    routing::{get, post},
    Router,
};
use parking_lot::Mutex;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::Semaphore;

/// Coordinator configuration.
#[derive(Clone, Debug)]
pub struct CoordinatorConfig {
    /// How long a worker may hold a task without renewing before the lease is reaped.
    pub lease_ttl_secs: u64,
    /// How long without a heartbeat before a worker is declared dead.
    pub worker_timeout_secs: u64,
}

impl Default for CoordinatorConfig {
    fn default() -> Self {
        CoordinatorConfig { lease_ttl_secs: 30, worker_timeout_secs: 60 }
    }
}

/// Shared handle cloned into every axum handler and background task.
#[derive(Clone)]
pub struct AppState {
    pub state:      Arc<Mutex<CoordinatorState>>,
    /// Semaphore whose permit count = tasks currently in the task queue.
    /// Workers acquire a permit before popping a task (long-poll).
    pub work_queue: Arc<Semaphore>,
}

/// Build and run the coordinator HTTP server on `addr`. Blocks until shutdown.
pub async fn start_server(config: CoordinatorConfig, addr: SocketAddr) {
    let lease_ttl     = Duration::from_secs(config.lease_ttl_secs);
    let worker_timeout = Duration::from_secs(config.worker_timeout_secs);

    let app_state = AppState {
        state:      Arc::new(Mutex::new(CoordinatorState::new(lease_ttl))),
        work_queue: Arc::new(Semaphore::new(0)),
    };

    // Background: reap expired leases and dead workers every 5 s.
    {
        let s = app_state.clone();
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(5));
            loop {
                interval.tick().await;
                let now = Instant::now();
                let (requeued_leases, requeued_workers) = {
                    let mut state = s.state.lock();
                    (state.reap_expired(now), state.reap_dead_workers(worker_timeout, now))
                };
                let total = requeued_leases + requeued_workers;
                if total > 0 {
                    s.work_queue.add_permits(total);
                    log::info!("reaper: re-queued {total} tasks ({requeued_leases} expired leases, {requeued_workers} dead workers)");
                }
            }
        });
    }

    let router = Router::new()
        // Client API
        .route("/v1/batch",              post(routes::submit_batch))
        .route("/v1/batch/:job_id",      get(routes::get_batch))
        .route("/v1/cube",               post(routes::submit_cube))
        .route("/v1/cube/:job_id",       get(routes::get_cube))
        // Worker API
        .route("/v1/work",               get(routes::get_work))
        .route("/v1/work/:task_id/result", post(routes::post_result))
        .route("/v1/work/:task_id/renew",  post(routes::renew_lease))
        .route("/v1/heartbeat",          post(routes::heartbeat))
        // Admin
        .route("/v1/status",             get(routes::status))
        .with_state(app_state);

    log::info!("rm-coordinator listening on {addr}");
    let listener = tokio::net::TcpListener::bind(addr).await
        .expect("bind failed");
    axum::serve(listener, router).await.expect("server error");
}
