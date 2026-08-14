use clap::{Parser, Subcommand};
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "reasonmesh", version, about = "ReasonMesh SMT solver")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Solve an SMT-LIB 2.7 problem file.
    Solve {
        /// Path to the .smt2 file.
        file: PathBuf,
        /// Number of CPU worker threads.
        #[arg(long, default_value = "1")]
        workers: u32,
        /// Random seed.
        #[arg(long, default_value = "1")]
        seed: u64,
        /// Run deterministically (single worker, fixed seed).
        #[arg(long)]
        deterministic: bool,
        /// Disable GPU workers.
        #[arg(long)]
        no_gpu: bool,
    },
    /// Replay a captured trace for debugging.
    Replay {
        trace: PathBuf,
    },
    /// Verify an UNSAT proof/certificate.
    CheckProof {
        proof: PathBuf,
    },
    /// Run a benchmark manifest.
    Benchmark {
        manifest: PathBuf,
    },
}

fn main() {
    env_logger::init();
    let cli = Cli::parse();

    match cli.command {
        Command::Solve { file, workers, seed, deterministic, no_gpu } => {
            let workers = if deterministic { 1 } else { workers };
            eprintln!("reasonmesh solve: {} workers={} seed={}", file.display(), workers, seed);
            eprintln!("(solver not yet implemented — M1 in progress)");
            std::process::exit(10); // exit code 10 = UNKNOWN
        }
        Command::Replay { trace } => {
            eprintln!("replay: {} (not yet implemented)", trace.display());
        }
        Command::CheckProof { proof } => {
            eprintln!("check-proof: {} (not yet implemented)", proof.display());
        }
        Command::Benchmark { manifest } => {
            eprintln!("benchmark: {} (not yet implemented)", manifest.display());
        }
    }
}
