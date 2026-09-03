use clap::Parser;
use rm_coordinator::{start_server, CoordinatorConfig};
use std::net::SocketAddr;

#[derive(Parser)]
#[command(
    name    = "rm-coordinator",
    about   = "ReasonMesh distributed coordinator — HTTP work queue for proof farms and cube-and-conquer",
    version
)]
struct Args {
    /// Address to listen on.
    #[arg(long, default_value = "0.0.0.0:7700")]
    addr: SocketAddr,

    /// Worker task lease TTL in seconds. Tasks not renewed within this window are re-queued.
    #[arg(long, default_value_t = 30)]
    lease_ttl_secs: u64,

    /// Seconds without a heartbeat before a worker is declared dead and its tasks re-queued.
    #[arg(long, default_value_t = 60)]
    worker_timeout_secs: u64,
}

#[tokio::main]
async fn main() {
    env_logger::Builder::from_env(
        env_logger::Env::default().default_filter_or("info"),
    )
    .init();

    let args = Args::parse();
    let config = CoordinatorConfig {
        lease_ttl_secs:      args.lease_ttl_secs,
        worker_timeout_secs: args.worker_timeout_secs,
    };
    start_server(config, args.addr).await;
}
