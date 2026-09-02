use serde::{Deserialize, Serialize};

/// Snapshot of a knowledge bus's operational metrics.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct BusMetrics {
    pub published_total: u64,
    pub polled_total: u64,
    pub deduplicated: u64,
    pub evicted: u64,
    /// Conditional objects removed because an unconditional version of the
    /// same conclusion entered the buffer (§12.4).
    pub superseded: u64,
    /// Publish calls that were rejected with `BufferFull` back-pressure.
    pub backpressure: u64,
    /// Connections dropped because the peer's schema version fell outside the
    /// negotiated range (network transport only).
    pub schema_rejected: u64,
    pub bytes_serialized: u64,
    pub bytes_received: u64,
    pub buffer_utilization: f32,
}
