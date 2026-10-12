use std::collections::{HashMap, VecDeque};
use std::net::SocketAddr;
use std::sync::{Arc, Mutex};

use tokio::net::{TcpListener, TcpStream};
use tokio::sync::Notify;

use crate::{
    framing,
    protocol::{CoordMsg, WorkerMsg},
    ClusterResult,
};

// ---------------------------------------------------------------------------
// Cube pool (shared state between connection handlers)
// ---------------------------------------------------------------------------

struct CubePool {
    pending: VecDeque<(u32, Vec<i32>)>,
    in_flight: HashMap<u32, (u32, Vec<i32>)>, // conn_id → (cube_id, assumptions)
    unsat_count: u32,
    total: u32,
    result: Option<ClusterResult>,
}

impl CubePool {
    fn new(cubes: Vec<Vec<i32>>) -> Self {
        let total = cubes.len() as u32;
        let pending = cubes
            .into_iter()
            .enumerate()
            .map(|(i, a)| (i as u32, a))
            .collect();
        CubePool {
            pending,
            in_flight: HashMap::new(),
            unsat_count: 0,
            total,
            result: None,
        }
    }

    fn assign(&mut self, conn_id: u32) -> Option<CoordMsg> {
        if self.result.is_some() {
            return None;
        }
        let (cube_id, assumptions) = self.pending.pop_front()?;
        self.in_flight.insert(conn_id, (cube_id, assumptions.clone()));
        Some(CoordMsg::AssignCube { cube_id, assumptions })
    }

    fn report_sat(&mut self, conn_id: u32) {
        self.in_flight.remove(&conn_id);
        self.result = Some(ClusterResult::Sat);
    }

    /// Returns true when all cubes are confirmed UNSAT (global UNSAT).
    fn report_unsat(&mut self, conn_id: u32) -> bool {
        if self.in_flight.remove(&conn_id).is_some() {
            self.unsat_count += 1;
        }
        if self.unsat_count == self.total && self.pending.is_empty() {
            self.result = Some(ClusterResult::Unsat);
            return true;
        }
        false
    }

    fn requeue(&mut self, conn_id: u32) {
        if let Some((cube_id, assumptions)) = self.in_flight.remove(&conn_id) {
            self.pending.push_front((cube_id, assumptions));
        }
    }
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Cluster coordinator: listens for worker connections, distributes cubes.
#[derive(Default)]
pub struct ClusterCoordinator;

/// Coordinator bound to a TCP port — ready to accept workers.
pub struct BoundCoordinator {
    pub addr: SocketAddr,
    listener: TcpListener,
}

impl ClusterCoordinator {
    /// Bind to `addr`.  Use port 0 for an OS-assigned ephemeral port.
    pub async fn bind(&self, addr: SocketAddr) -> std::io::Result<BoundCoordinator> {
        let listener = TcpListener::bind(addr).await?;
        let addr = listener.local_addr()?;
        Ok(BoundCoordinator { addr, listener })
    }
}

impl BoundCoordinator {
    /// Start solving.  Blocks until all cubes are resolved or a SAT answer is found.
    ///
    /// If `cubes` is empty the whole problem is treated as a single cube (empty
    /// assumptions).  Workers should connect before or shortly after this is called.
    pub async fn run(
        self,
        num_vars: u32,
        clauses: Vec<Vec<i32>>,
        cubes: Vec<Vec<i32>>,
    ) -> ClusterResult {
        let cubes = if cubes.is_empty() { vec![vec![]] } else { cubes };

        let pool = Arc::new(Mutex::new(CubePool::new(cubes)));
        let done = Arc::new(Notify::new());

        let problem = CoordMsg::Problem {
            num_vars,
            clauses,
        };

        let mut conn_id: u32 = 0;
        loop {
            tokio::select! {
                accept = self.listener.accept() => {
                    let Ok((stream, _)) = accept else { continue; };
                    let pool = Arc::clone(&pool);
                    let done = Arc::clone(&done);
                    let problem = problem.clone();
                    conn_id += 1;
                    let cid = conn_id;
                    tokio::spawn(async move {
                        handle_worker(cid, stream, problem, pool, done).await;
                    });
                }
                _ = done.notified() => {
                    break;
                }
            }
        }

        let result = pool.lock().unwrap()
            .result
            .clone()
            .unwrap_or(ClusterResult::Failed("no result produced".into()));
        result
    }
}

// ---------------------------------------------------------------------------
// Per-connection handler
// ---------------------------------------------------------------------------

async fn handle_worker(
    conn_id: u32,
    stream: TcpStream,
    problem: CoordMsg,
    pool: Arc<Mutex<CubePool>>,
    done: Arc<Notify>,
) {
    let (mut reader, mut writer) = tokio::io::split(stream);

    if framing::write_msg(&mut writer, &problem).await.is_err() {
        return;
    }

    loop {
        // Grab the next cube, or exit if the result is already known.
        let assign_msg = {
            let mut g = pool.lock().unwrap();
            g.assign(conn_id)
        };

        let Some(msg) = assign_msg else {
            // No pending cubes for this worker.
            return;
        };

        let _cube_id = match &msg {
            CoordMsg::AssignCube { cube_id, .. } => *cube_id,
            _ => return,
        };

        if framing::write_msg(&mut writer, &msg).await.is_err() {
            pool.lock().unwrap().requeue(conn_id);
            return;
        }

        let worker_msg: WorkerMsg = match framing::read_msg(&mut reader).await {
            Ok(m) => m,
            Err(_) => {
                // Worker disconnected: return cube to pool for reassignment.
                pool.lock().unwrap().requeue(conn_id);
                return;
            }
        };

        let finished = {
            let mut g = pool.lock().unwrap();
            match worker_msg {
                WorkerMsg::CubeSat { .. } => {
                    g.report_sat(conn_id);
                    true
                }
                WorkerMsg::CubeUnsat { .. } => g.report_unsat(conn_id),
            }
        };

        if finished {
            done.notify_one();
            return;
        }

        // Another handler may have set result = Sat between our receive and here.
        let cancelled = pool.lock().unwrap().result.is_some();
        if cancelled {
            let _ = framing::write_msg(&mut writer, &CoordMsg::Cancel).await;
            return;
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::worker_node::ClusterWorkerNode;

    async fn run_cluster(
        num_vars: u32,
        clauses: Vec<Vec<i32>>,
        cubes: Vec<Vec<i32>>,
        n_workers: usize,
    ) -> ClusterResult {
        let coord = ClusterCoordinator;
        let bound = coord
            .bind("127.0.0.1:0".parse().unwrap())
            .await
            .expect("bind");
        let addr = bound.addr;

        for _ in 0..n_workers {
            tokio::spawn(async move {
                ClusterWorkerNode::new(1).run(addr).await.ok();
            });
        }

        bound.run(num_vars, clauses, cubes).await
    }

    #[tokio::test]
    async fn test_single_cube_sat() {
        // x1 is satisfiable; one empty-assumption cube.
        let result = run_cluster(1, vec![vec![1]], vec![vec![]], 1).await;
        assert!(matches!(result, ClusterResult::Sat), "{result:?}");
    }

    #[tokio::test]
    async fn test_single_cube_unsat() {
        // x1 ∧ ¬x1 is unsatisfiable.
        let result = run_cluster(1, vec![vec![1], vec![-1]], vec![vec![]], 1).await;
        assert!(matches!(result, ClusterResult::Unsat), "{result:?}");
    }

    #[tokio::test]
    async fn test_two_cubes_sat() {
        // x1 ∨ x2; cube1 forces x1=true (SAT), cube2 forces x1=false.
        let result = run_cluster(
            2,
            vec![vec![1, 2]],
            vec![vec![1], vec![-1]],
            2,
        )
        .await;
        assert!(matches!(result, ClusterResult::Sat), "{result:?}");
    }

    #[tokio::test]
    async fn test_two_cubes_unsat() {
        // (x1 ∨ x2) ∧ (¬x1) ∧ (¬x2); both cubes are UNSAT.
        let result = run_cluster(
            2,
            vec![vec![1, 2], vec![-1], vec![-2]],
            vec![vec![1], vec![-1]],
            2,
        )
        .await;
        assert!(matches!(result, ClusterResult::Unsat), "{result:?}");
    }

    #[tokio::test]
    async fn test_three_cubes_one_worker() {
        // Same UNSAT formula, three cubes, one worker (sequential).
        let result = run_cluster(
            3,
            vec![vec![1, 2], vec![-1], vec![-2]],
            vec![vec![1], vec![-1, 2], vec![-1, -2]],
            1,
        )
        .await;
        // All cubes UNSAT.
        assert!(matches!(result, ClusterResult::Unsat), "{result:?}");
    }
}
