// Copyright 2025-2026 Cornell University
// released under MIT license
// author: Kevin Laeufer <laeufer@cornell.edu>

//! Coefficient Library

use num_bigint::{BigInt, BigUint, Sign};
use std::fmt::{Display, Formatter};
use std::ops::Shl;

/// The mod factor that we are using.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Mod {
    bytes: u32,
    words: u32,
    msb_mask: Word,
}

impl Mod {
    #[inline]
    pub const fn from_words(words: usize) -> Self {
        Self::from_bits(words as u32 * Word::BITS)
    }

    #[inline]
    pub fn from_factor(factor: &BigUint) -> Self {
        let ones = factor.count_ones();
        let is_power_of_two = ones == 1;
        assert!(is_power_of_two);
        let bits = factor.trailing_zeros().unwrap() as u32;
        Self::from_bits(bits)
    }

    #[inline]
    pub const fn from_bits(bits: u32) -> Self {
        // assert_eq!(bits % 8, 0);
        Self::from_bytes(bits / 8)
    }

    #[inline]
    const fn from_bytes(bytes: u32) -> Self {
        let bits = 8 * bytes;
        let words = bits.div_ceil(Word::BITS);
        let msb_mask = if bits.is_multiple_of(Word::BITS) {
            Word::MAX
        } else {
            ((1 as Word) << (bits % Word::BITS)) - 1
        };
        Self {
            bytes,
            words,
            msb_mask,
        }
    }

    #[inline]
    pub fn bits(&self) -> u32 {
        self.bytes() * 8
    }

    #[inline]
    pub fn bytes(&self) -> u32 {
        self.bytes
    }
    pub fn factor(&self) -> BigUint {
        BigUint::from(1u32).shl(self.bits() as usize)
    }

    #[inline]
    fn words(&self) -> usize {
        self.words as usize
    }

    #[inline]
    fn msb_mask(&self) -> Word {
        self.msb_mask
    }
}

/// A coefficient representation that can be used to perform variable substitution.
pub trait Coef: Clone {
    fn from_big(value: &BigInt, m: Mod) -> Self;
    fn from_i64(v: i64, m: Mod) -> Self;
    fn pow2(e: u32, m: Mod) -> Self;
    fn zero() -> Self;
    fn is_zero(&self) -> bool;
    fn assign_zero(&mut self);
    fn add_assign(&mut self, other: &Self, m: Mod);
    fn mul_assign(&mut self, other: &Self, m: Mod);
    const MAX_MOD: Mod;
}

type Word = u64;
type DoubleWord = u128;

/// Custom implementation of a fixed size coefficient using a static sized array.
#[derive(Debug, Clone, PartialEq)]
pub struct ArrayCoef<const W: usize> {
    /// Contain the actual number in big endian
    words: [Word; W],
}

// src: https://github.com/cucapra/baa/blob/1840f13d9a6bd9fa60de5b7a6326e96059d56b70/src/bv/arithmetic.rs#L204C1-L210C2
#[inline]
fn adc(carry: u8, a: &mut Word, b: Word) -> u8 {
    let sum = carry as DoubleWord + *a as DoubleWord + b as DoubleWord;
    *a = sum as Word;
    (sum >> Word::BITS) as u8
}

#[inline]
fn mul<const W: usize>(a: &mut [Word; W], b: &[Word; W]) {
    debug_assert_eq!(a.len(), b.len());
    let mut acc = [0 as Word; W];
    for (i, bi) in b.iter().enumerate() {
        mac_word(&mut acc[i..], a, *bi);
    }

    // acc contains the result
    a.copy_from_slice(&acc);
}

#[inline]
fn mac_word(acc: &mut [Word], b: &[Word], word: Word) {
    let mut carry = 0;
    for (a, b) in acc.iter_mut().zip(b) {
        *a = mac_with_carry(*a, *b, word, &mut carry);
    }
}

#[inline]
fn mac_with_carry(a: Word, b: Word, c: Word, acc: &mut DoubleWord) -> Word {
    *acc += a as DoubleWord;
    *acc += (b as DoubleWord) * (c as DoubleWord);
    let lo = *acc as Word;
    *acc >>= Word::BITS;
    lo
}

fn words_to_u32(words: &[Word]) -> Vec<u32> {
    debug_assert_eq!(u32::BITS * 2, Word::BITS);
    let mut words32 = Vec::with_capacity(words.len() * 2);
    let mask32 = u32::MAX as Word;
    for w in words.iter() {
        let word = *w;
        let lsb = (word & mask32) as u32;
        let msb = ((word >> 32) & mask32) as u32;
        words32.push(lsb);
        words32.push(msb);
    }
    words32
}

impl<const W: usize> ArrayCoef<W> {
    const MAX_BYTES: u32 = W as u32 * Word::BITS / 8;
    fn to_ubig(&self) -> BigUint {
        BigUint::from_slice(&words_to_u32(&self.words))
    }

    #[cfg(test)]
    fn from_words(words_in: &[Word], m: Mod) -> Self {
        debug_assert_eq!(words_in.len(), W);
        let mut words = [0 as Word; W];
        words.as_mut_slice().copy_from_slice(words_in);
        let mut r = Self { words };
        r.do_mask(m);
        r
    }

    #[inline]
    fn do_mask(&mut self, m: Mod) {
        // mask out upper words
        for w in self.words.iter_mut().skip(m.words()) {
            *w = 0;
        }
        self.words[m.words() - 1] &= m.msb_mask();
    }

    fn negate(&mut self, m: Mod) {
        // invert all
        for ii in 0..W {
            self.words[ii] = !self.words[ii];
        }
        // add one
        let mut carry = adc(0, &mut self.words[0], 1);
        for ii in 1..W {
            carry = adc(carry, &mut self.words[ii], 0);
        }
        self.do_mask(m);
    }

    fn from_ubig(value: &BigUint, m: Mod) -> Self {
        // iter_u64 returns lsb first which matches our convention
        let digits: Vec<Word> = value.iter_u64_digits().collect();
        let mut words = [0; W];
        words[0..digits.len()].copy_from_slice(&digits);
        let mut r = Self { words };
        r.do_mask(m);
        r
    }

    #[inline]
    fn from_u64(v: u64, m: Mod) -> Self {
        debug_assert!(m.bytes() <= Self::MAX_BYTES);
        debug_assert!(Self::MAX_BYTES * 8 >= u64::BITS);
        let mut r = Self::zero();
        r.words[0] = v as Word;
        r
    }
}

impl<const W: usize> Coef for ArrayCoef<W> {
    fn from_big(value: &BigInt, m: Mod) -> Self {
        let is_negative = value.sign() == Sign::Minus;
        let mut r = Self::from_ubig(value.magnitude(), m);
        if is_negative {
            r.negate(m);
        }
        r
    }

    #[inline]
    fn from_i64(v: i64, m: Mod) -> Self {
        Self::from_u64(v as u64, m)
    }

    fn pow2(e: u32, m: Mod) -> Self {
        let mut r = Self::zero();
        if m.bits() > e {
            let word_ii = e / Word::BITS;
            r.words[word_ii as usize] = (1 as Word) << (e % Word::BITS);
        }
        r
    }

    #[inline]
    fn zero() -> Self {
        Self { words: [0; W] }
    }

    fn is_zero(&self) -> bool {
        self.words.iter().all(|w| *w == 0)
    }

    fn assign_zero(&mut self) {
        for w in self.words.iter_mut() {
            *w = 0;
        }
    }

    fn add_assign(&mut self, other: &Self, m: Mod) {
        debug_assert!(m.bytes() <= Self::MAX_BYTES);
        let mut carry = 0;
        for ii in 0..W {
            carry = adc(carry, &mut self.words[ii], other.words[ii]);
        }
        self.do_mask(m);
    }

    fn mul_assign(&mut self, other: &Self, m: Mod) {
        debug_assert!(m.bytes() <= Self::MAX_BYTES);
        mul(&mut self.words, &other.words);
        self.do_mask(m);
    }

    const MAX_MOD: Mod = Mod::from_words(W);
}

impl<const W: usize> Display for ArrayCoef<W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_ubig())
    }
}

impl Coef for Word {
    fn from_big(value: &BigInt, m: Mod) -> Self {
        Self::from_i64(value.try_into().unwrap(), m)
    }

    fn from_i64(v: i64, m: Mod) -> Self {
        v as Word & m.msb_mask
    }

    fn pow2(e: u32, m: Mod) -> Self {
        debug_assert!(m.words == 1);
        if e < m.bits() { (1 as Word) << e } else { 0 }
    }

    fn zero() -> Self {
        0
    }

    fn is_zero(&self) -> bool {
        *self == 0
    }

    fn assign_zero(&mut self) {
        *self = 0;
    }

    fn add_assign(&mut self, other: &Self, m: Mod) {
        *self = self.overflowing_add(*other).0 & m.msb_mask;
    }

    fn mul_assign(&mut self, other: &Self, m: Mod) {
        *self = self.overflowing_mul(*other).0 & m.msb_mask;
    }

    const MAX_MOD: Mod = Mod::from_words(1);
}

#[inline]
fn mask_double_word(v: DoubleWord, m: Mod) -> DoubleWord {
    match m.words {
        0 => 0,
        1 => v & m.msb_mask as DoubleWord,
        2 => v & (((m.msb_mask as DoubleWord) << Word::BITS) | Word::MAX as DoubleWord),
        _ => unreachable!("u128 can only be used to represent up to two words!"),
    }
}

type SignedDoubleWord = i128;

impl Coef for DoubleWord {
    fn from_big(value: &BigInt, m: Mod) -> Self {
        let r: SignedDoubleWord = value.try_into().unwrap();
        mask_double_word(r as DoubleWord, m)
    }

    fn from_i64(v: i64, m: Mod) -> Self {
        mask_double_word(v as DoubleWord, m)
    }

    fn pow2(e: u32, m: Mod) -> Self {
        debug_assert!(m.words <= 2);
        if e < m.bits() {
            (1 as DoubleWord) << e
        } else {
            0
        }
    }

    fn zero() -> Self {
        0
    }

    fn is_zero(&self) -> bool {
        *self == 0
    }

    fn assign_zero(&mut self) {
        *self = 0;
    }

    fn add_assign(&mut self, other: &Self, m: Mod) {
        *self = mask_double_word(self.overflowing_add(*other).0, m);
    }

    fn mul_assign(&mut self, other: &Self, m: Mod) {
        *self = mask_double_word(self.overflowing_mul(*other).0, m);
    }

    const MAX_MOD: Mod = Mod::from_words(2);
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Num;

    fn do_test_mod(factor: &str, bits: u32, bytes: u32) {
        let factor = BigUint::from_str_radix(factor, 10).unwrap();
        let m = Mod::from_factor(&factor);
        assert_eq!(m.bytes(), bytes);
        assert_eq!(m.bits(), bits);
        assert_eq!(m.factor(), factor);
    }

    #[test]
    fn test_mod() {
        do_test_mod("4294967296", 32, 4);
        do_test_mod("18446744073709551616", 64, 8);
        do_test_mod("340282366920938463463374607431768211456", 128, 16);
        do_test_mod(
            "115792089237316195423570985008687907853269984665640564039457584007913129639936",
            256,
            32,
        );
        do_test_mod(
            "13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096",
            512,
            64,
        );
    }

    #[test]
    fn test_sizes() {
        assert_eq!(
            std::mem::size_of::<ArrayCoef::<1>>(),
            std::mem::size_of::<Word>()
        )
    }

    #[test]
    fn test_simple_coef_mod_64_bits_1_word() {
        let m = Mod::from_bits(64);
        let mut a = ArrayCoef::<1>::from_u64(2, m);
        let b = ArrayCoef::<1>::from_u64(1u64 << 63, m);
        a.mul_assign(&b, m);
        assert!(a.is_zero(), "{a:?}");
    }

    #[test]
    fn test_simple_coef_mod_64_u64() {
        let m = Mod::from_bits(64);
        let mut a = u64::from_i64(2, m);
        let b = u64::from_i64((1u64 << 63) as i64, m);
        a.mul_assign(&b, m);
        assert!(a.is_zero(), "{a:?}");
    }

    #[test]
    fn test_simple_coef_mod_64_bits_2_word() {
        let m = Mod::from_bits(64);
        let mut a = ArrayCoef::<2>::from_u64(2, m);
        let b = ArrayCoef::<2>::from_u64(1u64 << 63, m);
        a.mul_assign(&b, m);
        assert!(a.is_zero());
    }

    #[test]
    fn test_simple_coef_mod_128_bits_2_word() {
        let m = Mod::from_bits(128);
        let mut a = ArrayCoef::<2>::from_big(&BigInt::from_str_radix("-1", 10).unwrap(), m);
        let old_a = a.clone();
        let one = ArrayCoef::<2>::from_u64(1, m);
        a.add_assign(&one, m);
        assert!(a.is_zero(), "{old_a} + {one} = {a}");
    }

    #[test]
    fn test_simple_coef_mod_128_bits_u128() {
        let m = Mod::from_bits(128);
        let mut a = u128::from_big(&BigInt::from_str_radix("-1", 10).unwrap(), m);
        let old_a = a;
        let one = u128::from_i64(1, m);
        a.add_assign(&one, m);
        assert!(a.is_zero(), "{old_a} + {one} = {a}");
    }

    #[test]
    fn test_mul_256() {
        let m = Mod::from_bits(256);
        let a = ArrayCoef::<4>::from_words(&[0, 0xff << (Word::BITS - 8), 0, 0], m);
        let b = ArrayCoef::<4>::from_u64(2, m);
        let expect = ArrayCoef::<4>::from_words(&[0, 0xfe << (Word::BITS - 8), 1, 0], m);
        let mut res = a.clone();
        res.mul_assign(&b, m);
        assert_eq!(res, expect);

        let mut res2 = b.clone();
        res2.mul_assign(&a, m);
        assert_eq!(res2, expect);
    }
}
