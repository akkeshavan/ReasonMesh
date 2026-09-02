/// Eviction strategy when a scope-level buffer is full.
#[derive(Clone, Copy, Debug)]
pub enum EvictionPolicy {
    /// Evict the item with the lowest utility score; ties broken by age
    /// (oldest first, spec §12.3 node/worker-local).
    LowestUtility,
    /// Evict the lowest-utility item, and if utilities tie, the oldest one
    /// (spec §12.3 cluster/global).
    LowestUtilityThenOldest,
    /// Evict the oldest item regardless of utility.
    Oldest,
    /// Reject the incoming item (back-pressure to the producer).
    RejectIncoming,
}

/// Configuration for a bus instance.
#[derive(Clone, Debug)]
pub struct BusConfig {
    /// Maximum number of objects held in the local-scope buffer.
    pub local_buffer: usize,
    /// Maximum number of objects held in the process-scope buffer.
    pub process_buffer: usize,
    pub eviction: EvictionPolicy,
}

impl Default for BusConfig {
    fn default() -> Self {
        BusConfig {
            local_buffer: 8_192,
            process_buffer: 65_536,
            eviction: EvictionPolicy::LowestUtility,
        }
    }
}
