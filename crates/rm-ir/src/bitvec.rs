//! Bit-vector values with arbitrary width, stored little-endian
//! least-significant-bit first. Used for constant folding and model
//! evaluation.

use serde::{Deserialize, Serialize};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Bv {
    width: u32,
    bits: Vec<bool>,
}

impl Bv {
    pub fn from_bits(width: u32, bits: Vec<bool>) -> Self {
        debug_assert_eq!(width as usize, bits.len());
        Bv { width, bits }
    }

    pub fn zero(width: u32) -> Self {
        Bv { width, bits: vec![false; width as usize] }
    }

    pub fn from_u64(value: u64, width: u32) -> Self {
        let mut bits = Vec::with_capacity(width as usize);
        let mut v = value;
        for _ in 0..width {
            bits.push(v & 1 == 1);
            v >>= 1;
        }
        Bv { width, bits }
    }

    pub fn one(width: u32) -> Self {
        let mut b = Bv::zero(width);
        if width > 0 {
            b.bits[0] = true;
        }
        b
    }

    pub fn width(&self) -> u32 {
        self.width
    }

    pub fn len(&self) -> usize {
        self.width as usize
    }

    pub fn is_empty(&self) -> bool {
        self.width == 0
    }

    pub fn bit(&self, i: usize) -> bool {
        self.bits[i]
    }

    pub fn bits(&self) -> &[bool] {
        &self.bits
    }

    pub fn to_u64(&self) -> u64 {
        let mut v = 0u64;
        for (i, &b) in self.bits.iter().take(64).enumerate() {
            if b {
                v |= 1 << i;
            }
        }
        v
    }

    pub fn is_zero(&self) -> bool {
        self.bits.iter().all(|&b| !b)
    }

    /// Interpret the vector as a two's-complement signed integer.
    pub fn as_signed_i64(&self) -> i64 {
        let u = self.to_u64();
        match self.width {
            0 => 0,
            1 => {
                if self.bits[0] { -1 } else { 0 }
            }
            _ => {
                let sign = self.bits[self.width as usize - 1];
                let mask = (1u64 << (self.width - 1)) - 1u64;
                let body = u & mask;
                if sign { (body as i64) - (1i64 << (self.width - 1)) } else { body as i64 }
            }
        }
    }
}

impl fmt::Display for Bv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#b")?;
        for b in self.bits.iter().rev() {
            write!(f, "{}", if *b { '1' } else { '0' })?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_u64_reverses_with_to_u64() {
        let b = Bv::from_u64(0b1011, 4);
        assert_eq!(b.bits, vec![true, true, false, true]);
        assert_eq!(b.to_u64(), 0b1011);
        assert_eq!(b.to_string(), "#b1011");
    }

    #[test]
    fn signed_interpretation() {
        assert_eq!(Bv::zero(8).as_signed_i64(), 0);
        assert_eq!(Bv::from_u64(0xFF, 8).as_signed_i64(), -1);
        assert_eq!(Bv::from_u64(0x7F, 8).as_signed_i64(), 127);
        assert_eq!(Bv::from_u64(0x80, 8).as_signed_i64(), -128);
    }

    #[test]
    fn constants() {
        assert!(Bv::zero(8).is_zero());
        assert_eq!(Bv::one(8).to_u64(), 1);
        assert_eq!(Bv::one(1).to_u64(), 1);
        assert_eq!(Bv::from_u64(0, 0).width(), 0);
    }
}