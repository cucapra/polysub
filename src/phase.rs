// Copyright 2026 Cornell University
// released under MIT license
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{Coef, Mod, Polynom, Term, VarIndex};

/// Represent a polynomial which internally uses the phase change optimization from the
/// FMCAD'24 paper: "Symbolic Computer Algebra for Multipliers Revisited - It's All About Orders and Phases"
/// Note that `replace_var` is not directly supported. Instead, you will need to use the
/// `replace_...` methods specialized for particular gate types.
#[derive(Debug, Clone)]
pub struct PhaseOptPolynom<C: Coef> {
    inner: Polynom<C>,
    inverted: BitSet,
}

impl<C: Coef> PhaseOptPolynom<C> {
    pub fn new(m: Mod) -> Self {
        let inner = Polynom::new(m);
        let inverted = BitSet::new();
        Self { inner, inverted }
    }

    pub fn with_max_mod() -> Self {
        let inner = Polynom::with_max_mod();
        let inverted = BitSet::new();
        Self { inner, inverted }
    }

    pub fn from_monoms(m: Mod, monoms: impl Iterator<Item = (C, Term)>) -> Self {
        let inner = Polynom::from_monoms(m, monoms);
        // by default, no variables are inverted!
        let inverted = BitSet::new();
        Self { inner, inverted }
    }
}

impl<C: Coef> From<Polynom<C>> for PhaseOptPolynom<C> {
    fn from(inner: Polynom<C>) -> Self {
        // by default, no variables are inverted!
        let inverted = BitSet::new();
        Self { inner, inverted }
    }
}

/// Operations that transparently call the corresponding method in the underlying polynom.
impl<C: Coef> PhaseOptPolynom<C> {
    #[inline]
    pub fn size(&self) -> usize {
        self.inner.size()
    }
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }
    #[inline]
    pub fn get_mod(&self) -> Mod {
        self.inner.get_mod()
    }
    /// Currently only allows for increating the mod coefficient!
    #[inline]
    pub fn change_mod(&mut self, new_m: Mod) {
        self.inner.change_mod(new_m)
    }
}

/// Phase information and manipulation
impl<C: Coef> PhaseOptPolynom<C> {
    pub fn is_inverted(&self, var: VarIndex) -> bool {
        self.inverted.contains(var.into())
    }

    pub fn invert(&mut self, var: VarIndex) {
        // 1 - a
        let monoms = [
            (C::from_i64(1, self.get_mod()), vec![].into()),
            (C::from_i64(-1, self.get_mod()), vec![var].into()),
        ];
        self.inner.replace_var(var, &monoms);
        self.inverted.toggle(var.into());
    }
}

/// Routines to replace specific gate types
impl<C: Coef> PhaseOptPolynom<C> {
    pub fn replace_and(&mut self, out: VarIndex, a: VarIndex, b: VarIndex) {
        self.ensure_not_inverted(out);
        match (self.is_inverted(a), self.is_inverted(b)) {
            (false, false) => self.inner.replace_and(out, a, b),
            (true, false) => self.replace_and_one_inverted(out, b, a),
            (false, true) => self.replace_and_one_inverted(out, a, b),
            (true, true) => {
                // 1 - !a - !b + !a!b
                let monoms = [
                    (C::from_i64(1, self.get_mod()), vec![].into()),
                    (C::from_i64(-1, self.get_mod()), vec![a].into()),
                    (C::from_i64(-1, self.get_mod()), vec![b].into()),
                    (C::from_i64(1, self.get_mod()), vec![a, b].into()),
                ];
                self.inner.replace_var(out, &monoms);
            }
        }
    }

    fn replace_and_one_inverted(&mut self, out: VarIndex, normal: VarIndex, inverted: VarIndex) {
        // a - a!b
        let monoms = [
            (C::from_i64(1, self.get_mod()), vec![normal].into()),
            (
                C::from_i64(-1, self.get_mod()),
                vec![normal, inverted].into(),
            ),
        ];
        self.inner.replace_var(out, &monoms);
    }

    pub fn replace_or(&mut self, out: VarIndex, a: VarIndex, b: VarIndex) {
        self.ensure_not_inverted(out);
        match (self.is_inverted(a), self.is_inverted(b)) {
            (false, false) => self.inner.replace_or(out, a, b),
            (true, false) => self.replace_or_one_inverted(out, b, a),
            (false, true) => self.replace_or_one_inverted(out, a, b),
            (true, true) => {
                // 1 - !a!b
                let monoms = [
                    (C::from_i64(1, self.get_mod()), vec![].into()),
                    (C::from_i64(-1, self.get_mod()), vec![a, b].into()),
                ];
                self.inner.replace_var(out, &monoms);
            }
        }
    }

    fn replace_or_one_inverted(&mut self, out: VarIndex, normal: VarIndex, inverted: VarIndex) {
        // 1 - !b + a!b
        let monoms = [
            (C::from_i64(1, self.get_mod()), vec![].into()),
            (C::from_i64(-1, self.get_mod()), vec![inverted].into()),
            (
                C::from_i64(1, self.get_mod()),
                vec![normal, inverted].into(),
            ),
        ];
        self.inner.replace_var(out, &monoms);
    }

    pub fn replace_xor(&mut self, out: VarIndex, a: VarIndex, b: VarIndex) {
        self.ensure_not_inverted(out);
        match (self.is_inverted(a), self.is_inverted(b)) {
            // if both inputs to an xor are inverted, the polynomial is the same as the original xor
            (false, false) | (true, true) => self.inner.replace_xor(out, a, b),
            (true, false) | (false, true) => {
                // for xor it does not matter which one is inverted
                // 1 - a - !b + 2a!b
                let monoms = [
                    (C::from_i64(1, self.get_mod()), vec![].into()),
                    (C::from_i64(-1, self.get_mod()), vec![a].into()),
                    (C::from_i64(-1, self.get_mod()), vec![b].into()),
                    (C::from_i64(2, self.get_mod()), vec![a, b].into()),
                ];
                self.inner.replace_var(out, &monoms);
            }
        }
    }

    fn ensure_not_inverted(&mut self, var: VarIndex) {
        if self.is_inverted(var) {
            self.invert(var);
        }
    }

    pub fn replace_not(&mut self, out: VarIndex, a: VarIndex) {
        if self.is_inverted(out) == self.is_inverted(a) {
            // same phase
            self.inner.replace_not(out, a);
        } else {
            // inverted phases
            // just replace the name of the variable
            self.inner.replace_identity(out, a);
        }
    }

    pub fn replace_true(&mut self, out: VarIndex) {
        if self.is_inverted(out) {
            self.inner.replace_false(out);
        } else {
            self.inner.replace_true(out);
        }
    }

    pub fn replace_false(&mut self, out: VarIndex) {
        if self.is_inverted(out) {
            self.inner.replace_true(out);
        } else {
            self.inner.replace_false(out);
        }
    }
}

type BitSetWord = u64;

/// Simple implementation of a dynamically growing, dense bit set.
#[derive(Debug, Clone)]
struct BitSet {
    words: Vec<BitSetWord>,
}

impl BitSet {
    fn new() -> Self {
        Self { words: vec![] }
    }

    /// Removes from set if it is contained, adds if it is not part of the set.
    fn toggle(&mut self, index: usize) {
        let word_index = index / BitSetWord::BITS as usize;
        let bit = index % BitSetWord::BITS as usize;
        if word_index >= self.words.len() {
            self.words.resize(word_index + 1, 0);
        }
        self.words[word_index] ^= 1 << bit;
    }

    fn contains(&self, index: usize) -> bool {
        let word_index = index / BitSetWord::BITS as usize;
        let bit = index % BitSetWord::BITS as usize;
        if word_index >= self.words.len() {
            false
        } else {
            (self.words[word_index] >> bit) & 1 == 1
        }
    }
}
