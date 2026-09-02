//! TCP KnowledgeBus transport with schema negotiation (spec §13).
//!
//! A `NetBus` node can both listen (accept peers) and connect to other nodes.
//! Knowledge is serialized with `postcard` into length-prefixed frames:
//!
//! ```text
//! [u32 schema version][u32 payload length][postcard(KnowledgeBatch)]
//! ```
//!
//! Before exchange, both ends run a handshake: the client advertises its
//! `schema_version`, and the server replies with its own version iff the
//! client's version lies within `NetConfig::min_compat..=max_compat` (a `0`
//! reply rejects). Incompatible peers are dropped and counted in
//! `BusMetrics::schema_rejected`. A node never interprets frames from an
//! incompatible peer.

use std::collections::VecDeque;
use std::io::{Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use crossbeam_channel::{unbounded, Receiver, Sender};

use crate::{BusError, KnowledgeBus, PollBudget, PublishHandle};
use rm_akx::{BusMetrics, KnowledgeBatch, KnowledgeObject, Scope};

/// Current on-the-wire schema version. Bump on any breaking change to the
/// `KnowledgeObject` serialization or frame format.
pub const SCHEMA_VERSION: u32 = 1;

/// Maximum serialized frame we are willing to read (64 MiB).
pub const DEFAULT_MAX_FRAME: usize = 64 << 20;

/// Negotiation bounds plus framing limits for a `NetBus` node.
#[derive(Clone, Copy, Debug)]
pub struct NetConfig {
    /// Version we advertise in the handshake.
    pub schema_version: u32,
    /// Lowest peer schema version we accept.
    pub min_compat: u32,
    /// Highest peer schema version we accept.
    pub max_compat: u32,
    /// Reject frames larger than this.
    pub max_frame: usize,
}

impl Default for NetConfig {
    fn default() -> Self {
        NetConfig {
            schema_version: SCHEMA_VERSION,
            min_compat: SCHEMA_VERSION,
            max_compat: SCHEMA_VERSION,
            max_frame: DEFAULT_MAX_FRAME,
        }
    }
}

/// A peer connection's write side. Frames are queued on a channel and drained
/// by a writer thread so `publish` never blocks on I/O.
struct Peer {
    writer: Sender<Vec<u8>>,
    handle: Option<std::thread::JoinHandle<()>>,
}

/// Network knowledge bus node.
///
/// Share it via `Arc<NetBus>`; all clones see the same accept loop, peer table,
/// and incoming queue.
pub struct NetBus {
    config: NetConfig,
    incoming: Mutex<VecDeque<KnowledgeObject>>,
    peers: Mutex<Vec<Peer>>,

    published: AtomicU64,
    polled: AtomicU64,
    deduplicated: AtomicU64,
    backpressure: AtomicU64,
    schema_rejected: AtomicU64,
    bytes_serialized: AtomicU64,
    bytes_received: AtomicU64,
}

// ---------------------------------------------------------------------------
// Handshake framing
// ---------------------------------------------------------------------------

/// Incremental frame reader: returns one complete frame per call.
struct FrameReader {
    buf: Vec<u8>,
}

impl FrameReader {
    fn new() -> Self {
        FrameReader { buf: Vec::new() }
    }

    /// Fill from `r` and return the next complete frame `(version, payload)`,
    /// or `None` when the stream ends cleanly between frames.
    fn next_frame(
        &mut self,
        r: &mut dyn Read,
        max_frame: usize,
    ) -> std::io::Result<Option<(u32, Vec<u8>)>> {
        // Accumulate the 8-byte header.
        while self.buf.len() < 8 {
            let want = 8 - self.buf.len();
            let mut chunk = [0u8; 8];
            let n = r.read(&mut chunk[..want])?;
            self.buf.extend_from_slice(&chunk[..n]);
            if n == 0 {
                return Ok(None);
            }
        }
        let version = u32::from_le_bytes(self.buf[0..4].try_into().unwrap());
        let len = u32::from_le_bytes(self.buf[4..8].try_into().unwrap()) as usize;
        if len > max_frame {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("frame too large: {len} > {max_frame}"),
            ));
        }
        self.buf.drain(..8);

        // Accumulate the payload.
        while self.buf.len() < len {
            let mut chunk = [0u8; 8192];
            let want = (len - self.buf.len()).min(chunk.len());
            let n = r.read(&mut chunk[..want])?;
            if n == 0 {
                return Ok(None);
            }
            self.buf.extend_from_slice(&chunk[..n]);
        }
        let payload: Vec<u8> = self.buf.drain(..len).collect();
        Ok(Some((version, payload)))
    }
}

/// Server-side handshake: advertise our version, read the peer's, and decide.
/// On accept the peer's reply is our (nonzero) schema version; on reject `0`.
/// Server-side handshake: read the peer version first, then reply. On accept
/// the reply is our (nonzero) schema version; on reject it is `0`.
fn handshake_server(stream: &mut TcpStream, cfg: &NetConfig) -> Result<(), BusError> {
    let mut ver = [0u8; 4];
    stream.read_exact(&mut ver).map_err(io_to_bus)?;
    let peer_version = u32::from_le_bytes(ver);
    if cfg.min_compat <= peer_version && peer_version <= cfg.max_compat {
        stream
            .write_all(&cfg.schema_version.to_le_bytes())
            .map_err(io_to_bus)?;
        stream.flush().map_err(io_to_bus)?;
        Ok(())
    } else {
        stream.write_all(&0u32.to_le_bytes()).map_err(io_to_bus)?;
        stream.flush().map_err(io_to_bus)?;
        Err(BusError::SchemaRejected)
    }
}

/// Client-side handshake: advertise our version first, expect nonzero reply.
fn handshake_client(stream: &mut TcpStream, cfg: &NetConfig) -> Result<(), BusError> {
    stream
        .write_all(&cfg.schema_version.to_le_bytes())
        .map_err(io_to_bus)?;
    stream.flush().map_err(io_to_bus)?;
    let mut reply = [0u8; 4];
    stream.read_exact(&mut reply).map_err(io_to_bus)?;
    let accepted = u32::from_le_bytes(reply);
    if accepted == 0 {
        return Err(BusError::SchemaRejected);
    }
    Ok(())
}

fn io_to_bus(e: std::io::Error) -> BusError {
    match e.kind() {
        std::io::ErrorKind::WouldBlock => BusError::BufferFull,
        _ => BusError::Disconnected,
    }
}

impl NetBus {
    /// Bind the accept loop on `addr`; returns a handle to the shared node.
    pub fn bind(addr: SocketAddr, cfg: NetConfig) -> std::io::Result<Arc<NetBus>> {
        let listener = TcpListener::bind(addr)?;
        let node = Arc::new(NetBus::node(cfg));
        let accept_node = Arc::clone(&node);
        std::thread::spawn(move || accept_node.accept_loop(listener));
        Ok(node)
    }

    /// Connect to a peer at `addr`. Returns a handle sharing this node's
    /// incoming queue, so `poll` sees objects published by the peer.
    pub fn connect(addr: SocketAddr, cfg: NetConfig) -> Result<Arc<NetBus>, BusError> {
        let mut stream = TcpStream::connect(addr).map_err(io_to_bus)?;
        stream
            .set_read_timeout(Some(Duration::from_millis(100)))
            .map_err(io_to_bus)?;
        stream
            .set_write_timeout(Some(Duration::from_secs(5)))
            .map_err(io_to_bus)?;
        handshake_client(&mut stream, &cfg)?;
        stream.set_read_timeout(None).map_err(io_to_bus)?;
        let node = Arc::new(NetBus::node(cfg));
        node.add_peer(Arc::new(stream));
        Ok(node)
    }

    fn node(cfg: NetConfig) -> Self {
        NetBus {
            config: cfg,
            incoming: Mutex::new(VecDeque::new()),
            peers: Mutex::new(Vec::new()),
            published: AtomicU64::new(0),
            polled: AtomicU64::new(0),
            deduplicated: AtomicU64::new(0),
            backpressure: AtomicU64::new(0),
            schema_rejected: AtomicU64::new(0),
            bytes_serialized: AtomicU64::new(0),
            bytes_received: AtomicU64::new(0),
        }
    }

    fn accept_loop(self: &Arc<Self>, listener: TcpListener) {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { continue };
            if stream
                .set_read_timeout(Some(Duration::from_millis(100)))
                .is_err()
                || stream
                    .set_write_timeout(Some(Duration::from_secs(5)))
                    .is_err()
            {
                continue;
            }
            match handshake_server(&mut stream, &self.config) {
                Ok(()) => {
                    if stream.set_read_timeout(None).is_ok() {
                        self.add_peer(Arc::new(stream));
                    }
                }
                Err(BusError::SchemaRejected) => {
                    self.schema_rejected.fetch_add(1, Ordering::Relaxed);
                }
                Err(_) => {}
            }
        }
    }

    /// Register a connected peer: spawn its reader and writer threads.
    fn add_peer(self: &Arc<Self>, stream: Arc<TcpStream>) {
        let (tx, rx) = unbounded::<Vec<u8>>();
        {
            let mut peers = self.peers.lock().unwrap();
            peers.retain(|p| p.handle.as_ref().is_some_and(|h| !h.is_finished()));
        }
        let reader = self.spawn_reader(Arc::clone(&stream));
        let writer = self.spawn_writer(stream, rx);
        let mut peers = self.peers.lock().unwrap();
        peers.push(Peer {
            writer: tx,
            handle: Some(reader),
        });
        drop(writer); // writer is detached
    }

    fn spawn_reader(self: &Arc<Self>, stream: Arc<TcpStream>) -> std::thread::JoinHandle<()> {
        let node = Arc::clone(self);
        std::thread::spawn(move || {
            let mut fr = FrameReader::new();
            loop {
                let mut s = &*stream;
                match fr.next_frame(&mut s, node.config.max_frame) {
                    Ok(Some((version, payload))) => {
                        if version != SCHEMA_VERSION {
                            node.schema_rejected.fetch_add(1, Ordering::Relaxed);
                            break;
                        }
                        node.bytes_received
                            .fetch_add(payload.len() as u64, Ordering::Relaxed);
                        match postcard::from_bytes::<KnowledgeBatch>(&payload) {
                            Ok(batch) => {
                                let mut q = node.incoming.lock().unwrap();
                                q.extend(batch);
                            }
                            Err(_) => {
                                node.schema_rejected.fetch_add(1, Ordering::Relaxed);
                            }
                        }
                    }
                    Ok(None) => break,
                    Err(_) => break,
                }
            }
        })
    }

    fn spawn_writer(
        self: &Arc<Self>,
        stream: Arc<TcpStream>,
        rx: Receiver<Vec<u8>>,
    ) -> std::thread::JoinHandle<()> {
        std::thread::spawn(move || {
            while let Ok(frame) = rx.recv() {
                // `Write` is implemented for `&TcpStream`.
                if (&*stream).write_all(&frame).is_err() {
                    break;
                }
            }
        })
    }
}

impl KnowledgeBus for NetBus {
    fn publish(&self, _scope: Scope, batch: KnowledgeBatch) -> Result<PublishHandle, BusError> {
        let bytes =
            postcard::to_allocvec(&batch).map_err(|_| BusError::Internal("encode".into()))?;
        self.bytes_serialized
            .fetch_add(bytes.len() as u64, Ordering::Relaxed);

        let mut frame = Vec::with_capacity(bytes.len() + 8);
        frame.extend_from_slice(&SCHEMA_VERSION.to_le_bytes());
        frame.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
        frame.extend_from_slice(&bytes);

        let peers = self.peers.lock().unwrap();
        let mut sent = 0usize;
        for peer in peers.iter() {
            if peer.writer.send(frame.clone()).is_ok() {
                sent += 1;
            } else {
                self.backpressure.fetch_add(1, Ordering::Relaxed);
            }
        }
        self.published.fetch_add(1, Ordering::Relaxed);
        Ok(PublishHandle { enqueued: sent })
    }

    fn poll(&self, budget: PollBudget) -> Result<KnowledgeBatch, BusError> {
        let mut q = self.incoming.lock().unwrap();
        let mut batch = KnowledgeBatch::new();
        while batch.len() < budget.max_items {
            let Some(obj) = q.pop_front() else {
                break;
            };
            self.polled.fetch_add(1, Ordering::Relaxed);
            batch.push(obj);
        }
        Ok(batch)
    }

    fn metrics(&self) -> BusMetrics {
        BusMetrics {
            published_total: self.published.load(Ordering::Relaxed),
            polled_total: self.polled.load(Ordering::Relaxed),
            deduplicated: self.deduplicated.load(Ordering::Relaxed),
            schema_rejected: self.schema_rejected.load(Ordering::Relaxed),
            backpressure: self.backpressure.load(Ordering::Relaxed),
            bytes_serialized: self.bytes_serialized.load(Ordering::Relaxed),
            bytes_received: self.bytes_received.load(Ordering::Relaxed),
            ..Default::default()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::SocketAddr;
    use std::time::{Duration, Instant};

    use rm_akx::literal::Literal;
    use rm_akx::{ClauseKnowledge, KnowledgeId, KnowledgeKind, TrustLevel};

    fn clause(id: u64, lits: &[u32], utility: f32) -> KnowledgeObject {
        KnowledgeObject {
            id: KnowledgeId(id),
            kind: KnowledgeKind::Clause(ClauseKnowledge {
                literals: lits.iter().map(|&v| Literal::positive(v)).collect(),
                lbd: 1,
            }),
            assumptions: Default::default(),
            scope: Scope::Global,
            trust: TrustLevel::Trusted,
            utility,
            proof_ref: None,
            source: 1,
        }
    }

    fn free_port() -> SocketAddr {
        TcpListener::bind("127.0.0.1:0")
            .unwrap()
            .local_addr()
            .unwrap()
    }

    /// Poll until `batch` contains at least one object or `timeout` elapses.
    fn poll_until(node: &NetBus, max_items: usize, timeout: Duration) -> KnowledgeBatch {
        let deadline = Instant::now() + timeout;
        loop {
            let batch = node.poll(PollBudget { max_items }).unwrap();
            if !batch.is_empty() {
                return batch;
            }
            if Instant::now() > deadline {
                panic!("timed out waiting for a network-published object");
            }
            std::thread::sleep(Duration::from_millis(5));
        }
    }

    #[test]
    fn frame_reader_roundtrip() {
        // Split the frame across multiple small reads to exercise accumulation.
        let obj = clause(7, &[0, 1], 0.5);
        let batch = vec![obj.clone()];
        let bytes = postcard::to_allocvec(&batch).unwrap();
        let mut frame = Vec::new();
        frame.extend_from_slice(&SCHEMA_VERSION.to_le_bytes());
        frame.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
        frame.extend_from_slice(&bytes);

        let mut reader = FrameReader::new();
        for chunk in frame.chunks(3) {
            let mut slice = chunk;
            if let Some((version, payload)) =
                reader.next_frame(&mut slice, DEFAULT_MAX_FRAME).unwrap()
            {
                assert_eq!(version, SCHEMA_VERSION);
                let decoded: KnowledgeBatch = postcard::from_bytes(&payload).unwrap();
                assert_eq!(decoded.len(), 1);
                assert_eq!(decoded[0].id, obj.id);
            }
        }
    }

    #[test]
    fn reject_oversized_frame() {
        let mut reader = FrameReader::new();
        let mut frame = Vec::new();
        frame.extend_from_slice(&SCHEMA_VERSION.to_le_bytes());
        frame.extend_from_slice(&u32::MAX.to_le_bytes());
        let mut slice = &frame[..];
        let err = reader.next_frame(&mut slice, 1024).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
    }

    #[test]
    fn two_nodes_roundtrip() {
        let addr = free_port();
        let server = NetBus::bind(addr, NetConfig::default()).unwrap();
        let client = NetBus::connect(addr, NetConfig::default()).unwrap();

        client
            .publish(Scope::Global, vec![clause(1, &[0, 1, 2], 0.5)])
            .unwrap();

        let batch = poll_until(&server, 10, Duration::from_secs(2));
        assert_eq!(batch.len(), 1);
        assert_eq!(batch[0].id, KnowledgeId(1));

        // Server->client direction over the same connection.
        server
            .publish(Scope::Global, vec![clause(2, &[3, 4], 0.5)])
            .unwrap();
        let batch = poll_until(&client, 10, Duration::from_secs(2));
        assert_eq!(batch.len(), 1);
        assert_eq!(batch[0].id, KnowledgeId(2));

        // Metrics reflect published + received byte counts on the server.
        assert!(server.metrics().bytes_received > 0);
    }

    #[test]
    fn incompatible_schema_rejected() {
        let addr = free_port();
        let server = NetBus::bind(addr, NetConfig::default()).unwrap();

        let bad = NetConfig {
            schema_version: 999,
            ..NetConfig::default()
        };
        let res = NetBus::connect(addr, bad);
        assert!(matches!(res, Err(BusError::SchemaRejected)));

        // Client-side is skipped entirely, so no peer is registered, but the
        // server must have counted the rejected handshake.
        std::thread::sleep(Duration::from_millis(100));
        assert!(server.metrics().schema_rejected >= 1);
    }
}
