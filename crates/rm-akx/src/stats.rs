use serde::{Deserialize, Serialize};

/// Snapshot of a knowledge bus's operational metrics.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct BusMetrics {
    pub published_total: u64,
    pub polled_total: u64,
    pub deduplicated: u64,
    pub evicted: u64,
    pub bytes_serialized: u64,
    pub bytes_received: u64,
    pub buffer_utilization: f32,
}
