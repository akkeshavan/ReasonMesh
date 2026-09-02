//! Efficient context structures for the AKX import predicate (§7.3).
//!
//! Two pre-filters that avoid the O(|asmpts|) subset merge in most cases:
//!
//! - `BloomFilter` over a worker's active context `ctx_W`. Used to pre-screen
//!   an assumption set: if the filter reports an assumption literal definitely
//!   absent, the object is skipped before the exact `ctx ⊇ asmpts` merge.
//!   A Bloom filter never produces false negatives, so skipping on "definitely
//!   absent" is always sound.
//!
//! - `ZobristContext` computes a rolling XOR fingerprint of `ctx_W`. Order
//!   independent and incrementally maintainable, so workers can publish a
//!   context hash with each export and the fabric can route knowledge to
//!   workers whose fingerprint matches a pre-computed compatible-context set
//!   (§7.3 "Assumption context hash").

use crate::literal::Literal;
use serde::{Deserialize, Serialize};

/// A simple splitmix64-based deterministic PRNG used to build the Bloom hash
/// functions and the Zobrist table deterministically (so all workers agree on
/// fingerprints without exchanging random tables).
pub struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    pub fn new(seed: u64) -> Self {
        SplitMix64 { state: seed }
    }
    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    /// A `u64` hash of `x` (deterministic across processes).
    pub fn hash64(x: u64) -> u64 {
        let mut z = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// A Bloom filter over a universe of literals.
///
/// `num_bits` (the filter size in bits) and `num_hashes` (k hash functions)
/// control the false-positive rate. The filter never returns false negatives:
/// `maybe_contains` returning `false` means the element is definitely absent.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BloomFilter {
    bits: BitVec,
    num_hashes: u32,
}

impl BloomFilter {
    /// Create an empty filter with `num_bits` bits and `num_hashes` hash
    /// functions. Sensible defaults: ~10 bits per expected element, 4 hashes.
    pub fn new(num_bits: usize, num_hashes: u32) -> Self {
        BloomFilter {
            bits: BitVec::new(num_bits),
            num_hashes: num_hashes.max(1),
        }
    }

    /// Build a filter containing the given context literals.
    pub fn over(lits: &[Literal], num_bits: usize, num_hashes: u32) -> Self {
        let mut f = BloomFilter::new(num_bits, num_hashes);
        for l in lits {
            f.insert(*l);
        }
        f
    }

    /// The number of bits in the filter.
    pub fn num_bits(&self) -> usize {
        self.bits.len_bits
    }

    pub fn insert(&mut self, lit: Literal) {
        for i in 0..self.num_hashes {
            let idx = self.index(lit, i);
            self.bits.set(idx, true);
        }
    }

    /// `true` if the literal may be present. `false` = definitely absent.
    pub fn maybe_contains(&self, lit: Literal) -> bool {
        for i in 0..self.num_hashes {
            if !self.bits.get(self.index(lit, i)) {
                return false;
            }
        }
        true
    }

    /// Pre-filter for the subset check: `false` means at least one assumption
    /// literal is definitely absent, so `ctx ⊇ asmpts` cannot hold and the
    /// exact merge can be skipped. When `true` the caller must still perform
    /// the exact `ImportContext::contains_all`.
    pub fn maybe_contains_all(&self, asmpts: &[Literal]) -> bool {
        asmpts.iter().all(|l| self.maybe_contains(*l))
    }

    #[inline]
    fn index(&self, lit: Literal, hash_i: u32) -> usize {
        let (h1, h2) = Self::indices(lit.raw() as u64, self.num_hashes);
        let len = self.bits.len_bits.max(1) as u64;
        (h1.wrapping_add(h2.wrapping_mul(hash_i as u64)) % len) as usize
    }

    fn indices(raw: u64, num_hashes: u32) -> (u64, u64) {
        // A deterministic u64 hash of the raw literal id.
        let h1 = SplitMix64::hash64(raw);
        // Second hash must be nonzero and independent.
        let h2 = SplitMix64::hash64(raw ^ 0x9E37_79B9_7F4A_7C15).max(1);
        let _ = num_hashes;
        (h1, h2)
    }
}

/// A dense vector of bits.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct BitVec {
    len_bits: usize,
    words: Vec<u64>,
}

impl BitVec {
    fn new(len_bits: usize) -> Self {
        BitVec {
            len_bits,
            words: vec![0; len_bits.div_ceil(64)],
        }
    }
    #[inline]
    fn set(&mut self, idx: usize, value: bool) {
        if idx >= self.len_bits {
            return;
        }
        let w = idx / 64;
        let b = idx % 64;
        let mask = 1u64 << b;
        if value {
            self.words[w] |= mask;
        } else {
            self.words[w] &= !mask;
        }
    }
    #[inline]
    fn get(&self, idx: usize) -> bool {
        if idx >= self.len_bits {
            return false;
        }
        let w = idx / 64;
        let b = idx % 64;
        self.words[w] & (1 << b) != 0
    }
}

/// Rolling, order-independent XOR fingerprint of an assumption context.
///
/// Every worker builds its table from the same `seed`, so fingerprints are
/// comparable across processes. `add`/`remove` maintain the hash in O(1).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ZobristContext {
    /// `table[lit.raw() as usize]` — deterministic per seed.
    table: Vec<u64>,
    current: u64,
}

impl ZobristContext {
    /// Build a table covering variables `1..=num_vars` (both polarities) from
    /// a deterministic seed. `num_vars` need only cover the largest variable
    /// that will ever appear in a context.
    pub fn new(num_vars: u32, seed: u64) -> Self {
        let mut rng = SplitMix64::new(seed);
        let n = (num_vars as usize + 1) * 2;
        let mut table = Vec::with_capacity(n);
        for _ in 0..n {
            table.push(rng.next_u64());
        }
        ZobristContext { table, current: 0 }
    }

    /// XOR-in a literal. Returns the updated fingerprint.
    pub fn add(&mut self, lit: Literal) -> u64 {
        self.current ^= self.value(lit);
        self.current
    }

    /// XOR-out a literal. Returns the updated fingerprint (or `None` if the
    /// literal's index is out of the table's range).
    pub fn remove(&mut self, lit: Literal) -> Option<u64> {
        let val = self.table.get(lit.raw() as usize).copied()?;
        self.current ^= val;
        Some(self.current)
    }

    pub fn fingerprint(&self) -> u64 {
        self.current
    }

    /// Static fingerprint of a literal set, independent of any instance.
    pub fn fingerprint_of(lits: &[Literal], num_vars: u32, seed: u64) -> u64 {
        let mut z = ZobristContext::new(num_vars, seed);
        for l in lits {
            z.add(*l);
        }
        z.fingerprint()
    }

    #[inline]
    fn value(&self, lit: Literal) -> u64 {
        self.table.get(lit.raw() as usize).copied().unwrap_or(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bloom_never_false_negative() {
        let ctx_lits = [
            Literal::positive(1),
            Literal::negative(3),
            Literal::positive(5),
            Literal::negative(8),
        ];
        let bloom = BloomFilter::over(&ctx_lits, 256, 4);
        for l in ctx_lits {
            assert!(bloom.maybe_contains(l));
        }
        // Subset of the context must survive the pre-filter.
        let subset = [Literal::positive(1), Literal::negative(8)];
        assert!(bloom.maybe_contains_all(&subset));
        // Definitely-absent literal must be caught.
        assert!(!bloom.maybe_contains(Literal::positive(42)));
    }

    #[test]
    fn bloom_prefilter_never_blocks_true_subsets_fuzz() {
        let mut rng = SplitMix64::new(7);
        for _ in 0..200 {
            let ctx: Vec<Literal> = (0..12)
                .map(|_| {
                    let v = 1 + (rng.next_u64() % 8) as u32;
                    if rng.next_u64() & 1 == 0 {
                        Literal::positive(v)
                    } else {
                        Literal::negative(v)
                    }
                })
                .collect();
            let bloom = BloomFilter::over(&ctx, 512, 4);
            let subset: Vec<Literal> = ctx
                .iter()
                .copied()
                .filter(|_| rng.next_u64() & 1 == 0)
                .collect();
            // No false negatives: a real subset always passes the pre-filter.
            assert!(
                bloom.maybe_contains_all(&subset),
                "false negative on {subset:?}"
            );
        }
    }

    #[test]
    fn bloom_is_deterministic() {
        let ctx = [Literal::positive(2), Literal::negative(4)];
        let a = BloomFilter::over(&ctx, 128, 3);
        let b = BloomFilter::over(&ctx, 128, 3);
        assert_eq!(a.bits.words, b.bits.words);
    }

    #[test]
    fn zobrist_is_order_independent() {
        let lits = [
            Literal::positive(1),
            Literal::negative(2),
            Literal::positive(3),
        ];
        let f1 = ZobristContext::fingerprint_of(&lits, 4, 99);
        let mut reversed = lits;
        reversed.reverse();
        let f2 = ZobristContext::fingerprint_of(&reversed, 4, 99);
        assert_eq!(f1, f2);
    }

    #[test]
    fn zobrist_incremental_matches_static() {
        let mut z = ZobristContext::new(5, 42);
        z.add(Literal::negative(2));
        z.add(Literal::positive(1));
        // {¬x2, x1} built incrementally == static set fingerprint.
        let set = vec![Literal::positive(1), Literal::negative(2)];
        let static_fp = ZobristContext::fingerprint_of(&set, 5, 42);
        assert_eq!(z.fingerprint(), static_fp);
        // Adding a duplicate breaks set semantics (XOR toggles); callers must
        // maintain a set. Verify the documented contract holds: adding an
        // already-present literal would toggle it back out.
        z.add(Literal::negative(2));
        let not_dupe: Vec<Literal> = vec![Literal::positive(1)];
        assert_eq!(
            z.fingerprint(),
            ZobristContext::fingerprint_of(&not_dupe, 5, 42)
        );
    }

    #[test]
    fn zobrist_remove_inverts_add() {
        let mut z = ZobristContext::new(5, 1);
        let before = z.fingerprint();
        z.add(Literal::positive(3));
        z.add(Literal::negative(1));
        let mid = z.fingerprint();
        assert_ne!(before, mid);
        let only_x3 = ZobristContext::fingerprint_of(&[Literal::positive(3)], 5, 1);
        assert_eq!(z.remove(Literal::negative(1)), Some(only_x3));
        assert_eq!(z.fingerprint(), only_x3);
    }

    #[test]
    fn zobrist_deterministic_across_instances() {
        let lits = [Literal::positive(1), Literal::negative(2)];
        let a = ZobristContext::fingerprint_of(&lits, 5, 77);
        let b = ZobristContext::fingerprint_of(&lits, 5, 77);
        assert_eq!(a, b);
    }
}
