//! Shared GPU service thread.
//!
//! One `GpuService` owns the Metal/CUDA backend and processes walk requests
//! from multiple CPU workers sequentially — no GPU contention. Each worker
//! holds a cheap `GpuClient` clone (a channel handle) and blocks in `walk()`
//! only for as long as the GPU needs to finish its job.
//!
//! Usage:
//! ```ignore
//! let (service, client) = GpuService::start(Box::new(MetalAccelerator::new()?));
//! // hand one clone to each worker:
//! worker0.set_gpu(Box::new(client.clone()));
//! worker1.set_gpu(Box::new(client.clone()));
//! // service lives until dropped (after all workers have finished)
//! ```

use crate::{GpuAccelerator, GpuClause, WalkResult};
use std::sync::mpsc;

struct ServiceMsg {
    clauses:          Vec<GpuClause>,
    num_vars:         u32,
    initial_polarity: Vec<bool>,
    seed:             u64,
    num_trajectories: u32,
    steps_per_var:    u32,
    reply:            mpsc::SyncSender<WalkResult>,
}

/// Owns the GPU service thread. Drop after all `GpuClient`s are done.
pub struct GpuService {
    handle: Option<std::thread::JoinHandle<()>>,
}

impl Drop for GpuService {
    fn drop(&mut self) {
        if let Some(h) = self.handle.take() {
            // The thread exits on its own once all SyncSenders (GpuClients) are
            // dropped; joining here just waits for that clean exit.
            let _ = h.join();
        }
    }
}

/// Cloneable handle to the shared GPU service. Each clone is a new `SyncSender`
/// to the same channel — the service processes one request at a time from the
/// shared queue, so there is no GPU contention between workers.
#[derive(Clone)]
pub struct GpuClient {
    tx:     mpsc::SyncSender<ServiceMsg>,
    device: String,
}

impl GpuService {
    /// Start the GPU service thread backed by `backend`.
    ///
    /// Returns `(service, client)`. Clone `client` and hand one copy to each
    /// CDCL worker via `solver.set_gpu(Box::new(client.clone()))`.
    /// The service thread runs until all `GpuClient` clones are dropped.
    pub fn start(backend: Box<dyn GpuAccelerator + Send>) -> (GpuService, GpuClient) {
        let device = backend.device_name().to_owned();
        // Bound of 64: enough back-pressure so workers never spin hard, but
        // small enough to avoid unbounded queuing if the GPU falls behind.
        let (tx, rx) = mpsc::sync_channel::<ServiceMsg>(64);
        let handle = std::thread::Builder::new()
            .name("rm-gpu-service".into())
            .spawn(move || {
                for msg in rx {
                    let result = backend.walk(
                        &msg.clauses,
                        msg.num_vars,
                        &msg.initial_polarity,
                        msg.seed,
                        msg.num_trajectories,
                        msg.steps_per_var,
                    );
                    // Ignore send error: worker may have timed out and dropped reply_rx.
                    let _ = msg.reply.send(result);
                }
            })
            .expect("spawn rm-gpu-service");
        let client = GpuClient { tx, device };
        (GpuService { handle: Some(handle) }, client)
    }
}

impl GpuAccelerator for GpuClient {
    fn walk(
        &self,
        clauses: &[GpuClause],
        num_vars: u32,
        initial_polarity: &[bool],
        seed: u64,
        num_trajectories: u32,
        steps_per_var: u32,
    ) -> WalkResult {
        let (reply_tx, reply_rx) = mpsc::sync_channel(1);
        let msg = ServiceMsg {
            clauses: clauses.to_vec(),
            num_vars,
            initial_polarity: initial_polarity.to_vec(),
            seed,
            num_trajectories,
            steps_per_var,
            reply: reply_tx,
        };
        if self.tx.send(msg).is_err() {
            // Service thread gone; return empty result (caller's guard will skip write-back).
            return WalkResult {
                polarity: vec![false; num_vars as usize + 1],
                sat_count: 0,
            };
        }
        reply_rx.recv().unwrap_or(WalkResult {
            polarity: vec![false; num_vars as usize + 1],
            sat_count: 0,
        })
    }

    fn device_name(&self) -> &str {
        &self.device
    }
}
