//! Shared bounded ring-buffer queue with §12.3 eviction and §12.4 supersede
//! semantics. Used by both the in-process bus and the hierarchical router.

use crate::{BusError, EvictionPolicy};
use rm_akx::{
    knowledge::{canonical_key, conclusion_key},
    KnowledgeObject,
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::collections::{BinaryHeap, VecDeque};

/// Outcome of inserting one object into a [`Queue`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InsertOutcome {
    /// The object was accepted into the buffer.
    Inserted {
        /// Number of conditional versions of the same conclusion that were
        /// evicted as superseded (§12.4).
        superseded: usize,
        /// Number of items evicted to make room (§12.3).
        evicted: usize,
    },
    /// Duplicate of an object already buffered (same canonical key).
    Duplicate,
    /// Redundant: a conditional whose conclusion already has an unconditional
    /// version buffered, or an unconditional already present.
    Redundant,
}

// ---------------------------------------------------------------------------
// D1-3: EvictEntry for the min-heap
// ---------------------------------------------------------------------------

/// An entry in the eviction min-heap (lowest utility at top).
///
/// `utility_bits` is `f32::to_bits()`. IEEE 754 bit-pattern ordering is
/// monotone for non-negative floats (which utility values always are), so
/// comparing bit patterns gives the correct order.
#[derive(Eq, PartialEq)]
struct EvictEntry {
    utility_bits: u32,
    id: u64,
}

impl Ord for EvictEntry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Min-heap: lower utility_bits = higher priority for eviction.
        // We use `Reverse` at the call site, so natural ordering here is fine.
        self.utility_bits
            .cmp(&other.utility_bits)
            .then(self.id.cmp(&other.id))
    }
}

impl PartialOrd for EvictEntry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// The bounded ring buffer plus the indexing needed for dedup/supersede/evict.
pub(crate) struct Queue {
    buf: VecDeque<KnowledgeObject>,
    cap: usize,
    eviction: EvictionPolicy,
    /// Canonical keys of objects currently buffered.
    keys: FxHashSet<u64>,
    /// Conclusion keys that have an unconditional version currently buffered.
    /// A conditional of such a conclusion is redundant and dropped on arrival.
    unconditional: FxHashSet<u64>,

    // D1-3: parallel min-heap for O(log n) lowest-utility eviction.
    /// Min-heap ordered by (utility_bits, id) ascending. Entries may be stale
    /// (lazy deletion): valid only if `id` is still in `active_ids`.
    eviction_heap: BinaryHeap<std::cmp::Reverse<EvictEntry>>,
    /// Set of IDs currently alive in `buf`. Used for lazy heap deletion.
    active_ids: FxHashSet<u64>,

    // D1-4: tombstone-based O(1) remove_conditionals.
    /// IDs that have been logically deleted but not yet compacted out of `buf`.
    deleted: FxHashSet<u64>,
    /// conclusion_key → Vec of entry IDs that are conditional on that key.
    conditional_index: FxHashMap<u64, Vec<u64>>,
}

impl Queue {
    pub(crate) fn new(cap: usize, eviction: EvictionPolicy) -> Self {
        Queue {
            buf: VecDeque::with_capacity(cap.min(1024)),
            cap: cap.max(1),
            eviction,
            keys: FxHashSet::default(),
            unconditional: FxHashSet::default(),
            eviction_heap: BinaryHeap::new(),
            active_ids: FxHashSet::default(),
            deleted: FxHashSet::default(),
            conditional_index: FxHashMap::default(),
        }
    }

    /// Number of objects currently buffered (excluding tombstoned entries).
    pub(crate) fn len(&self) -> usize {
        self.buf.len() - self.deleted.len()
    }

    /// Capacity of the buffer.
    pub(crate) fn cap(&self) -> usize {
        self.cap
    }

    /// Collect `(index, clone)` pairs for all buffered objects satisfying
    /// `pred`, in buffer order. Used by the hierarchy to decide promotion
    /// without losing place.
    pub(crate) fn enumerate_where(
        &self,
        pred: impl Fn(&KnowledgeObject) -> bool,
    ) -> Vec<(usize, KnowledgeObject)> {
        self.buf
            .iter()
            .enumerate()
            .filter(|(_, o)| !self.deleted.contains(&o.id.0) && pred(o))
            .map(|(i, o)| (i, o.clone()))
            .collect()
    }

    /// Collect `(id, utility)` pairs for all buffered (non-deleted) objects
    /// whose utility is at or above `min_utility`. No full clone.
    pub(crate) fn enumerate_ids_above_utility(
        &self,
        min_utility: f32,
    ) -> Vec<(u64, f32)> {
        self.buf
            .iter()
            .filter(|o| !self.deleted.contains(&o.id.0) && o.utility >= min_utility)
            .map(|o| (o.id.0, o.utility))
            .collect()
    }

    /// Fetch the object with the given `id` by scanning the buffer.
    /// Returns `None` if it has been evicted or tombstoned.
    pub(crate) fn get_by_id(&self, id: u64) -> Option<KnowledgeObject> {
        self.buf
            .iter()
            .find(|o| o.id.0 == id && !self.deleted.contains(&id))
            .cloned()
    }

    /// Insert `obj`, applying dedup/supersede/eviction.
    ///
    /// Returns `Ok(InsertOutcome)` on success, or
    /// `Err(BusError::BufferFull)` if the incoming item must be rejected under
    /// back-pressure. `Err(BusError::BufferFull)` leaves the buffer unchanged.
    pub(crate) fn insert(&mut self, obj: KnowledgeObject) -> Result<InsertOutcome, BusError> {
        let ck = conclusion_key(&obj);
        let key = canonical_key(&obj);

        if self.keys.contains(&key) {
            return Ok(InsertOutcome::Duplicate);
        }

        if obj.is_unconditional() {
            let superseded = self.remove_conditionals(ck);
            if self.unconditional.contains(&ck) {
                return Ok(InsertOutcome::Redundant);
            }
            let evicted = self.make_room(obj.utility)?;
            self.unconditional.insert(ck);
            self.keys.insert(key);
            self.push_to_buf(obj);
            Ok(InsertOutcome::Inserted {
                superseded,
                evicted,
            })
        } else {
            if self.unconditional.contains(&ck) {
                return Ok(InsertOutcome::Redundant);
            }
            let evicted = self.make_room(obj.utility)?;
            // D1-4: record in conditional index before push.
            let id = obj.id.0;
            self.conditional_index
                .entry(ck)
                .or_default()
                .push(id);
            self.keys.insert(key);
            self.push_to_buf(obj);
            Ok(InsertOutcome::Inserted {
                superseded: 0,
                evicted,
            })
        }
    }

    /// Push an object into `buf` and update eviction bookkeeping.
    fn push_to_buf(&mut self, obj: KnowledgeObject) {
        let id = obj.id.0;
        let ubits = obj.utility.to_bits();
        self.buf.push_back(obj);
        self.active_ids.insert(id);
        self.eviction_heap
            .push(std::cmp::Reverse(EvictEntry { utility_bits: ubits, id }));
    }

    /// Pop the front-most (oldest) non-deleted object.
    pub(crate) fn pop_front(&mut self) -> Option<KnowledgeObject> {
        loop {
            let removed = self.buf.pop_front()?;
            let id = removed.id.0;
            if self.deleted.contains(&id) {
                // Tombstoned: discard and continue.
                self.deleted.remove(&id);
                self.active_ids.remove(&id);
                // Also remove from keys / unconditional (deferred cleanup).
                self.keys.remove(&canonical_key(&removed));
                if removed.is_unconditional() {
                    self.unconditional.remove(&conclusion_key(&removed));
                }
                continue;
            }
            self.keys.remove(&canonical_key(&removed));
            if removed.is_unconditional() {
                self.unconditional.remove(&conclusion_key(&removed));
            }
            self.active_ids.remove(&id);
            return Some(removed);
        }
    }

    /// Evict and forget a buffered object at `index` in `buf`, returning it.
    fn evict_at(&mut self, index: usize) -> KnowledgeObject {
        let removed = self.buf.remove(index).expect("index in range");
        let id = removed.id.0;
        self.keys.remove(&canonical_key(&removed));
        if removed.is_unconditional() {
            self.unconditional.remove(&conclusion_key(&removed));
        }
        self.active_ids.remove(&id);
        // Heap entry stays; it will be skipped by lazy deletion.
        removed
    }

    /// D1-4: Remove all conditional versions of `ck` from the buffer (§12.4).
    /// Uses tombstoning for O(1) amortised cost. Returns the number removed.
    fn remove_conditionals(&mut self, ck: u64) -> usize {
        let ids = match self.conditional_index.remove(&ck) {
            Some(v) => v,
            None => return 0,
        };
        let mut removed = 0;
        for id in ids {
            if self.active_ids.contains(&id) {
                self.deleted.insert(id);
                self.active_ids.remove(&id);
                removed += 1;
            }
        }
        // Compact buf if tombstone ratio exceeds 50%.
        if self.deleted.len() > self.buf.len() / 2 {
            self.compact();
        }
        removed
    }

    /// Drain `buf`, filtering out tombstoned entries and rebuilding.
    fn compact(&mut self) {
        let old: VecDeque<KnowledgeObject> = std::mem::take(&mut self.buf);
        self.eviction_heap.clear();
        for obj in old {
            let id = obj.id.0;
            if self.deleted.contains(&id) {
                // Already accounted for in keys/unconditional cleanup in pop_front.
                // Handle keys cleanup here since pop_front won't see it.
                self.keys.remove(&canonical_key(&obj));
                if obj.is_unconditional() {
                    self.unconditional.remove(&conclusion_key(&obj));
                }
                self.deleted.remove(&id);
            } else {
                let ubits = obj.utility.to_bits();
                self.buf.push_back(obj);
                self.eviction_heap
                    .push(std::cmp::Reverse(EvictEntry { utility_bits: ubits, id }));
            }
        }
    }

    /// D1-3: Index of the lowest-utility buffered item whose utility is
    /// strictly below `incoming`, if any. Uses the min-heap for O(log n)
    /// amortised cost (lazy deletion of stale/tombstoned entries).
    fn lowest_utility_below(&mut self, incoming: f32) -> Option<usize> {
        // Pop stale entries from the heap until we find an active one.
        loop {
            let entry = match self.eviction_heap.peek() {
                Some(std::cmp::Reverse(e)) => (e.utility_bits, e.id),
                None => return None,
            };
            let (ubits, id) = entry;
            // Skip tombstoned or already-evicted entries (lazy deletion).
            if !self.active_ids.contains(&id) {
                self.eviction_heap.pop();
                continue;
            }
            let utility = f32::from_bits(ubits);
            if utility >= incoming {
                return None; // lowest active entry is not below incoming
            }
            // Find the actual index in buf.
            if let Some(idx) = self.buf.iter().position(|o| o.id.0 == id) {
                return Some(idx);
            }
            // Should not happen, but clean up and retry.
            self.eviction_heap.pop();
        }
    }

    /// Apply the configured eviction policy to make room for an incoming item.
    /// Returns `Ok(evicted_count)` if room was made (possibly 0), or
    /// `Err(BusError::BufferFull)` if the incoming item must be rejected.
    fn make_room(&mut self, incoming_utility: f32) -> Result<usize, BusError> {
        if self.len() < self.cap {
            return Ok(0);
        }
        match self.eviction {
            EvictionPolicy::Oldest => {
                // Pop from buf skipping tombstones.
                loop {
                    if self.buf.is_empty() {
                        return Err(BusError::BufferFull);
                    }
                    let front = &self.buf[0];
                    if self.deleted.contains(&front.id.0) {
                        // Remove tombstone from front.
                        let removed = self.buf.pop_front().unwrap();
                        self.deleted.remove(&removed.id.0);
                        self.active_ids.remove(&removed.id.0);
                        self.keys.remove(&canonical_key(&removed));
                        if removed.is_unconditional() {
                            self.unconditional.remove(&conclusion_key(&removed));
                        }
                        continue;
                    }
                    break;
                }
                self.evict_at(0);
                Ok(1)
            }
            EvictionPolicy::LowestUtility | EvictionPolicy::LowestUtilityThenOldest => {
                if let Some(index) = self.lowest_utility_below(incoming_utility) {
                    self.eviction_heap.pop(); // remove the heap entry we peeked
                    self.evict_at(index);
                    Ok(1)
                } else {
                    Err(BusError::BufferFull)
                }
            }
            EvictionPolicy::RejectIncoming => Err(BusError::BufferFull),
        }
    }
}
