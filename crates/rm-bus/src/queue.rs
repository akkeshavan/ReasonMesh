//! Shared bounded ring-buffer queue with §12.3 eviction and §12.4 supersede
//! semantics. Used by both the in-process bus and the hierarchical router.

use crate::{BusError, EvictionPolicy};
use rm_akx::{
    knowledge::{canonical_key, conclusion_key},
    KnowledgeObject,
};
use rustc_hash::FxHashSet;
use std::collections::VecDeque;

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
}

impl Queue {
    pub(crate) fn new(cap: usize, eviction: EvictionPolicy) -> Self {
        Queue {
            buf: VecDeque::with_capacity(cap.min(1024)),
            cap: cap.max(1),
            eviction,
            keys: FxHashSet::default(),
            unconditional: FxHashSet::default(),
        }
    }

    /// Number of objects currently buffered.
    pub(crate) fn len(&self) -> usize {
        self.buf.len()
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
            .filter(|(_, o)| pred(o))
            .map(|(i, o)| (i, o.clone()))
            .collect()
    }

    /// Insert `obj`, applying dedup/supersede/eviction.
    ///
    /// Returns `Ok(InsertOutcome)` on success, or
    /// `Err(BusError::BufferFull)` if the incoming item must be rejected under
    /// back-pressure. `Err(BusError::BufferFull)` leaves the buffer unchanged.
    pub(crate) fn insert(&mut self, obj: KnowledgeObject) -> Result<InsertOutcome, BusError> {
        let ck = conclusion_key(&obj);
        let key = canonical_key(&obj);

        // Hard dedup: identical conclusion + assumptions already buffered.
        if self.keys.contains(&key) {
            return Ok(InsertOutcome::Duplicate);
        }

        if obj.is_unconditional() {
            // §12.4: an unconditional version supersedes buffered conditionals
            // of the same conclusion.
            let superseded = self.remove_conditionals(ck);
            if self.unconditional.contains(&ck) {
                // We already hold the stronger version.
                return Ok(InsertOutcome::Redundant);
            }
            let evicted = self.make_room(obj.utility)?;
            self.unconditional.insert(ck);
            self.keys.insert(key);
            self.buf.push_back(obj);
            Ok(InsertOutcome::Inserted {
                superseded,
                evicted,
            })
        } else {
            if self.unconditional.contains(&ck) {
                // A conditional is redundant while the unconditional exists.
                return Ok(InsertOutcome::Redundant);
            }
            let evicted = self.make_room(obj.utility)?;
            self.keys.insert(key);
            self.buf.push_back(obj);
            Ok(InsertOutcome::Inserted {
                superseded: 0,
                evicted,
            })
        }
    }

    /// Pop the front-most (oldest) object.
    pub(crate) fn pop_front(&mut self) -> Option<KnowledgeObject> {
        let removed = self.buf.pop_front()?;
        self.keys.remove(&canonical_key(&removed));
        if removed.is_unconditional() {
            self.unconditional.remove(&conclusion_key(&removed));
        }
        Some(removed)
    }

    /// Evict and forget a buffered object at `index`, returning it.
    fn evict_at(&mut self, index: usize) -> KnowledgeObject {
        let removed = self.buf.remove(index).expect("index in range");
        self.keys.remove(&canonical_key(&removed));
        if removed.is_unconditional() {
            self.unconditional.remove(&conclusion_key(&removed));
        }
        removed
    }

    /// Remove all conditional versions of `ck` from the buffer (§12.4).
    /// Returns the number removed.
    fn remove_conditionals(&mut self, ck: u64) -> usize {
        let mut removed = 0;
        let mut i = self.buf.len();
        while i > 0 {
            i -= 1;
            let obj = &self.buf[i];
            if !obj.is_unconditional() && conclusion_key(obj) == ck {
                let key = canonical_key(obj);
                self.keys.remove(&key);
                self.buf.remove(i);
                removed += 1;
            }
        }
        removed
    }

    /// Index of the lowest-utility buffered item whose utility is strictly
    /// below `incoming`, if any. On ties selects the oldest (front-most),
    /// matching both §12.3 node and cluster policies.
    fn lowest_utility_below(&self, incoming: f32) -> Option<usize> {
        let mut best: Option<(usize, f32)> = None;
        for (i, o) in self.buf.iter().enumerate() {
            let u = o.utility;
            match best {
                None if u < incoming => best = Some((i, u)),
                Some((_, lu)) if u < lu => best = Some((i, u)),
                _ => {}
            }
        }
        best.map(|(i, _)| i)
    }

    /// Apply the configured eviction policy to make room for an incoming item.
    /// Returns `Ok(evicted_count)` if room was made (possibly 0), or
    /// `Err(BusError::BufferFull)` if the incoming item must be rejected.
    fn make_room(&mut self, incoming_utility: f32) -> Result<usize, BusError> {
        if self.buf.len() < self.cap {
            return Ok(0);
        }
        match self.eviction {
            EvictionPolicy::Oldest => {
                self.evict_at(0);
                Ok(1)
            }
            EvictionPolicy::LowestUtility | EvictionPolicy::LowestUtilityThenOldest => {
                if let Some(index) = self.lowest_utility_below(incoming_utility) {
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
