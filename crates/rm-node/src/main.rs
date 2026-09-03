//! rm-node — distributed solver worker.
//!
//! Polls an `rm-coordinator` for tasks, solves each SMT-LIB 2 script on a
//! blocking thread, and reports SAT / UNSAT / UNKNOWN back. Lease renewal runs
//! concurrently so the coordinator does not reap slow jobs.
//!
//! ## Operation
//!
//! ```text
//! rm-node --coordinator http://leader:7700 --concurrency 8
//! ```
//!
//! Each of the `--concurrency` slots runs an independent poll → solve → report
//! loop. A background heartbeat task pings the coordinator every 15 seconds so
//! the coordinator can detect dead workers.
//!
//! ## Cube splitting
//!
//! Workers do not split automatically in this release. A future version will
//! run a look-ahead heuristic and report `"split": [...]` when the local
//! conflict budget is exhausted, allowing the coordinator to fan the cube out
//! to more nodes.

mod loop_;

use clap::Parser;
use std::time::Duration;
use tokio::task::JoinSet;

#[derive(Parser, Debug, Clone)]
#[command(
    name    = "rm-node",
    about   = "ReasonMesh distributed solver node",
    version
)]
pub struct Args {
    /// Base URL of the rm-coordinator (no trailing slash).
    #[arg(long, default_value = "http://127.0.0.1:7700")]
    pub coordinator: String,

    /// Worker ID reported to the coordinator. Defaults to the OS process ID,
    /// which is unique on a single machine. Pass an explicit value (e.g. a
    /// Kubernetes pod index) when running across multiple hosts.
    #[arg(long)]
    pub worker_id: Option<u32>,

    /// Number of SMT tasks to solve in parallel on this node.
    #[arg(long, default_value_t = 4)]
    pub concurrency: u32,

    /// How long (ms) the /v1/work long-poll blocks waiting for a task.
    /// Should be shorter than the coordinator's lease TTL.
    #[arg(long, default_value_t = 25_000)]
    pub long_poll_ms: u64,

    /// Back-off (ms) between retry attempts when the coordinator is unreachable.
    #[arg(long, default_value_t = 2_000)]
    pub retry_ms: u64,
}

#[tokio::main]
async fn main() {
    env_logger::Builder::from_env(
        env_logger::Env::default().default_filter_or("info"),
    )
    .init();

    let args = Args::parse();
    let worker_id = args.worker_id.unwrap_or_else(std::process::id);

    log::info!(
        "rm-node starting: worker_id={worker_id} coord={} concurrency={}",
        args.coordinator,
        args.concurrency,
    );

    let client = reqwest::Client::builder()
        // Outer timeout = long_poll + 10 s slack for coordinator processing.
        .timeout(Duration::from_millis(args.long_poll_ms + 10_000))
        .build()
        .expect("build HTTP client");

    // Background heartbeat: keeps the worker entry alive in the coordinator's
    // worker table so dead-worker detection doesn't fire spuriously.
    {
        let client  = client.clone();
        let coord   = args.coordinator.clone();
        let retry   = Duration::from_millis(args.retry_ms);
        tokio::spawn(async move {
            loop_::heartbeat_loop(client, coord, worker_id, retry).await;
        });
    }

    // Spawn `concurrency` independent solve loops.
    let mut set = JoinSet::new();
    for slot in 0..args.concurrency {
        let client = client.clone();
        let args   = args.clone();
        set.spawn(async move {
            log::debug!("slot {slot} started");
            loop_::solve_loop(client, args, worker_id).await;
        });
    }

    // Loops run forever; wait for all (they shouldn't return).
    while set.join_next().await.is_some() {}
}
