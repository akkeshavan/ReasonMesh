use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

use tokio::net::TcpStream;

use rm_sat::{ParallelCdclSolver, ParallelConfig, SolveResult};

use crate::{
    framing,
    protocol::{CoordMsg, WorkerMsg},
};

/// Cluster worker node: connects to a coordinator and solves assigned cubes.
pub struct ClusterWorkerNode {
    /// Number of local CDCL threads per cube (0 = use all logical CPUs).
    pub local_threads: usize,
}

impl ClusterWorkerNode {
    pub fn new(local_threads: usize) -> Self {
        ClusterWorkerNode { local_threads }
    }

    /// Connect to `coordinator_addr`, receive cubes, solve, report results.
    /// Accepts any address form that tokio can resolve (IP:port or host:port).
    /// Returns when the coordinator closes the connection or an error occurs.
    pub async fn run(
        &self,
        coordinator_addr: impl tokio::net::ToSocketAddrs,
    ) -> std::io::Result<()> {
        let stream = TcpStream::connect(coordinator_addr).await?;
        let (mut reader, mut writer) = tokio::io::split(stream);

        // First message is always Problem.
        let first: CoordMsg = framing::read_msg(&mut reader).await?;
        let (num_vars, base_clauses) = match first {
            CoordMsg::Problem { num_vars, clauses } => (num_vars, clauses),
            _ => {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "expected Problem as first message",
                ))
            }
        };

        let local_threads = self.local_threads;

        loop {
            // Wait for the next coordinator message.
            let msg: CoordMsg = match framing::read_msg(&mut reader).await {
                Ok(m) => m,
                Err(_) => return Ok(()), // EOF = coordinator done
            };

            match msg {
                CoordMsg::AssignCube { cube_id, assumptions } => {
                    // Build the sub-problem: original clauses + unit clauses for assumptions.
                    let mut all_clauses = base_clauses.clone();
                    for lit in &assumptions {
                        all_clauses.push(vec![*lit]);
                    }

                    let ext_cancel = Arc::new(AtomicBool::new(false));
                    let config = ParallelConfig {
                        num_threads: local_threads,
                        ..Default::default()
                    };
                    let solver = Arc::new(ParallelCdclSolver::from_dimacs(
                        num_vars,
                        &all_clauses,
                        config,
                    ));
                    let solver_for_thread = Arc::clone(&solver);
                    let ext_for_thread = Arc::clone(&ext_cancel);

                    // Run the blocking solve concurrently with watching for Cancel (EOF).
                    let solve_handle = tokio::task::spawn_blocking(move || {
                        solver_for_thread.solve_with_cancel(ext_for_thread)
                    });

                    tokio::pin!(solve_handle);

                    let result = tokio::select! {
                        r = &mut solve_handle => r.unwrap_or(SolveResult::Unknown),
                        // Any incoming message while solving is a Cancel or protocol error.
                        _ = async {
                            // Discard the message; its presence alone is the signal.
                            let _: std::result::Result<CoordMsg, _> =
                                framing::read_msg(&mut reader).await;
                        } => {
                            ext_cancel.store(true, Ordering::SeqCst);
                            // Let the blocking thread finish its current slice (< 100 ms).
                            let _ = solve_handle.await;
                            return Ok(());
                        }
                    };

                    match result {
                        SolveResult::Sat(_) => {
                            framing::write_msg(&mut writer, &WorkerMsg::CubeSat { cube_id })
                                .await?;
                        }
                        SolveResult::Unsat => {
                            framing::write_msg(&mut writer, &WorkerMsg::CubeUnsat { cube_id })
                                .await?;
                        }
                        _ => {
                            // Cancelled / Unknown — coordinator has moved on.
                            return Ok(());
                        }
                    }
                }

                // Coordinator signals termination.
                CoordMsg::Cancel | CoordMsg::Problem { .. } => return Ok(()),
            }
        }
    }
}
