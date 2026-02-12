// Copyright 2025-2026 Cornell University
// released under MIT license
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::coef::{Coef, Mod};
use crate::varmap::{TermId, VarMap};
use indexmap::IndexMap;
use rustc_hash::FxBuildHasher;
use std::cmp::Ordering;
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::str::FromStr;

/// Represents a polynomial.
/// Contains additional data structures to allow for fast variable substitution.
#[derive(Debug, Clone)]
pub struct Polynom<C: Coef> {
    /// The module factor.
    m: Mod,
    /// Ordered map from term to coefficient.
    monoms: IndexMap<Term, C, FxBuildHasher>,
    /// List of all terms with a zero coefficient.
    zero_terms: Vec<TermId>,
    /// Fast access to the terms for each variable. Needs to be kept in sync with the monoms map.
    var_map: VarMap,
}

impl<C: Coef> Polynom<C> {
    pub fn new(m: Mod) -> Self {
        Self {
            m,
            monoms: IndexMap::default(),
            zero_terms: vec![],
            var_map: VarMap::new(),
        }
    }

    pub fn with_max_mod() -> Self {
        Self::new(C::MAX_MOD)
    }

    pub fn from_monoms(m: Mod, monoms: impl Iterator<Item = (C, Term)>) -> Self {
        let mut p = Self::new(m);
        for (coef, m) in monoms {
            p.add_monom(m, coef);
        }
        p
    }

    pub fn size(&self) -> usize {
        let size = self.monoms.len() - self.zero_terms.len();
        debug_assert_eq!(self.monoms.values().filter(|c| !c.is_zero()).count(), size);
        size
    }

    pub fn is_zero(&self) -> bool {
        self.size() == 0
    }

    pub fn get_mod(&self) -> Mod {
        self.m
    }

    /// Currently only allows for increating the mod coefficient!
    pub fn change_mod(&mut self, new_m: Mod) {
        if new_m.bits() > self.m.bits() {
            self.m = new_m;
        } else if new_m.bits() < self.m.bits() {
            todo!("update all coefficients to make sure they obey the mod!")
        }
    }

    pub fn sorted_monom_vec(&self) -> Vec<(C, Term)> {
        let mut r: Vec<_> = self
            .monoms
            .iter()
            .filter(|(_, c)| !c.is_zero())
            .map(|(value, key)| (key.clone(), value.clone()))
            .collect();
        r.sort_unstable_by(|(_, a), (_, b)| a.cmp(b));
        r
    }

    fn add_monom(&mut self, term: Term, coef: C) {
        // nothing to do if the coefficient is already zero
        if coef.is_zero() {
            return;
        }

        // do we already have a monom with the same term?
        if let Some((term_index, _, old_coef)) = self.monoms.get_full_mut(&term) {
            // if the old coefficient was zero, we need to remove the term index from the free list
            // and add the term back to the variable map
            if old_coef.is_zero() {
                let term_id: TermId = term_index.into();
                let pos = self.zero_terms.iter()
                    .position(|&t| t == term_id)
                    .expect("since the coefficient is zero, this term should be part of the zero_terms list!");
                // this changes the order, but that does not matter
                self.zero_terms.swap_remove(pos);
                self.var_map.add_term(&term, term_id);
            }

            // add the new coefficient to the old one
            old_coef.add_assign(&coef, self.m);

            // if the coefficients add up to zero, we need to remove the monom
            if old_coef.is_zero() {
                let term_id: TermId = term_index.into();
                // remove from the var map
                self.var_map.remove_term(&term, term_id);
                // remember the id so that the slot can get re-used
                self.zero_terms.push(term_id);
                // note: the actual term stays in the hash map in order to keep TermIds stable
            }
            // if the coefficient isn't zero, there is nothing more to do
        } else {
            // this is a new term, and we need to allocate a term id for it
            if let Some(term_id) = self.zero_terms.pop() {
                // insert term into var map
                self.var_map.add_term(&term, term_id);
                // replace the old term that was using this id
                self.monoms.replace_index(term_id.into(), term).unwrap();
                // store the new coefficient
                self.monoms[usize::from(term_id)] = coef;
            } else {
                // allocate space in the hash map
                let (term_index, old_coef) = self.monoms.insert_full(term, coef);
                debug_assert!(
                    old_coef.is_none(),
                    "There should never exist an equivalent term already."
                );
                // insert into var map
                let term = self.monoms.get_index(term_index).unwrap().0;
                self.var_map.add_term(term, term_index.into());
            }
        }
    }

    pub fn replace_var(&mut self, target: VarIndex, mons: &[(C, Term)]) {
        // collect all terms that we are interested in
        let todo: Vec<_> = self.var_map.terms_for_var(target).collect();

        // generate new terms
        let mut new_terms: Vec<_> = todo
            .iter()
            .flat_map(|&old_term_id| {
                let (old_term, old_coef) = self.monoms.get_index(old_term_id.into()).unwrap();
                let m = self.m;
                mons.iter().map(move |(new_coef, new_term)| {
                    debug_assert!(!new_coef.is_zero());
                    let mut combined_coef = old_coef.clone();
                    combined_coef.mul_assign(new_coef, m);
                    (old_term.replace_var(target, new_term), combined_coef)
                })
            })
            .collect();

        // remove old terms since they have been replaced
        // note: this can only happen after generating the new terms
        for old_term_id in todo.into_iter() {
            let old_term_index: usize = old_term_id.into();
            // remove from variable lookup map
            self.var_map.remove_term(
                self.monoms.get_index(old_term_index).unwrap().0,
                old_term_id,
            );
            // zero out old term
            self.monoms[old_term_index].assign_zero();
            self.zero_terms.push(old_term_id);
        }

        // sort new terms
        new_terms.sort_by(|(t1, _), (t2, _)| t1.cmp(t2));

        // apply new terms
        let mut new_term_iter = new_terms.into_iter();
        let (mut term, mut coef) = new_term_iter.next().unwrap();
        for (mut next_term, mut next_coef) in new_term_iter {
            if next_term != term {
                // update to new term
                std::mem::swap(&mut term, &mut next_term);
                std::mem::swap(&mut coef, &mut next_coef);
                // next_term now contains the _old_ term and next_coef the _old_ coef
                self.add_monom(next_term, next_coef);
            } else {
                coef.add_assign(&next_coef, self.m);
            }
        }
        // handle final term
        self.add_monom(term, coef);
    }

    /// The sum (modulo M) across all coefficient of the polynomial.
    /// Since we are in the digital domain this is the maximum value the polynomial could ever
    /// evaluate to.
    pub fn coef_sum(&self) -> C {
        let mut r = C::zero();
        for (_, c) in self.monoms.iter() {
            r.add_assign(c, self.m);
        }
        r
    }
}

/// Algebra routines built on core functionality.
impl<C: Coef> Polynom<C> {
    /// Adds the `other` polynomial to `self`.
    pub fn add_assign(&mut self, other: &Self) {
        assert_eq!(self.m, other.m, "Polynomial mod coefficients must match.");
        for (term, coef) in other.monoms.iter() {
            self.add_monom(term.clone(), coef.clone());
        }
    }

    /// Creates a new polynomial which is the product of `self` and `other`.
    pub fn mul(&self, other: &Self) -> Self {
        assert_eq!(self.m, other.m, "Polynomial mod coefficients must match.");
        let mut r = Self::new(self.m);
        for (term_a, coef_a) in self.monoms.iter() {
            for (term_b, coef_b) in other.monoms.iter() {
                let term = term_a.mul(term_b);
                let mut coef = coef_a.clone();
                coef.mul_assign(coef_b, self.m);
                r.add_monom(term, coef);
            }
        }
        r
    }

    /// Scale all monomials with the given coefficient.
    pub fn scale(&mut self, coef: &C) {
        for (_, c) in self.monoms.iter_mut() {
            c.mul_assign(coef, self.m);
        }
    }
}

impl<C: Coef + Display> Display for Polynom<C> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_zero() {
            write!(f, "0 (empty polynomial)")
        } else {
            let monoms = self.sorted_monom_vec();
            for (ii, (coef, term)) in monoms.iter().enumerate() {
                let is_last = ii == monoms.len() - 1;
                write!(f, "[{coef}*{term}]")?;
                if !is_last {
                    write!(f, " + ")?;
                }
            }
            Ok(())
        }
    }
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, Ord, PartialOrd)]
pub struct VarIndex(u32);

impl Display for VarIndex {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "x{}", self.0)
    }
}

impl From<u32> for VarIndex {
    fn from(v: u32) -> Self {
        Self(v)
    }
}

impl From<VarIndex> for u32 {
    fn from(value: VarIndex) -> Self {
        value.0
    }
}

impl From<VarIndex> for usize {
    fn from(value: VarIndex) -> Self {
        value.0 as usize
    }
}

#[derive(Debug, Clone, Eq)]
pub struct Term {
    vars: Vec<VarIndex>,
    // sum over all variables
    sum: u32,
}

impl Term {
    fn new(mut vars: Vec<VarIndex>) -> Self {
        vars.sort();
        let sum = vars.iter().map(|v| v.0).sum();
        Self { vars, sum }
    }

    fn replace_var(&self, target: VarIndex, other: &Term) -> Self {
        self.internal_replace_var(Some(target), other)
    }

    /// Combines two terms, essentially multiplying them.
    /// This is very similar to the replace_var method, just that no variable is removed.
    fn mul(&self, other: &Term) -> Self {
        if self.vars.is_empty() {
            return other.clone();
        }
        if other.vars.is_empty() {
            return self.clone();
        }

        self.internal_replace_var(None, other)
    }

    // Replace var, but the actual replacing is optional
    #[inline]
    fn internal_replace_var(&self, target: Option<VarIndex>, other: &Term) -> Self {
        debug_assert!(!self.vars.is_empty());

        let mut a_iter = self.vars.iter();
        let mut b_iter = other.vars.iter();
        let mut a_next = a_iter.next();
        let mut b_next = b_iter.next();

        let mut vars = Vec::with_capacity(self.vars.len() + other.vars.len() - 1);
        let mut sum = 0;
        let mut add_var = |value: VarIndex| {
            if vars.last().map(|l| *l < value).unwrap_or(true) {
                sum += value.0;
                vars.push(value);
            }
        };
        while a_next.is_some() || b_next.is_some() {
            match (a_next.cloned(), b_next.cloned()) {
                (Some(a), None) => {
                    if Some(a) != target {
                        add_var(a);
                    }
                    a_next = a_iter.next();
                }
                (None, Some(b)) => {
                    add_var(b);
                    b_next = b_iter.next();
                }
                (Some(a), Some(b)) => match a.cmp(&b) {
                    Ordering::Less => {
                        if Some(a) != target {
                            add_var(a);
                        }
                        a_next = a_iter.next();
                    }
                    Ordering::Equal => {
                        if Some(a) != target {
                            // this should never be true because it means that the target is part of the replacement
                            add_var(a);
                        }
                        a_next = a_iter.next();
                        b_next = b_iter.next();
                    }
                    Ordering::Greater => {
                        add_var(b);
                        b_next = b_iter.next();
                    }
                },
                (None, None) => unreachable!("loop should have terminated"),
            }
        }

        debug_assert!(
            vars.as_slice().windows(2).all(|w| w[0] < w[1]),
            "{:?}",
            vars
        );

        // note: do not call `new` here to avoid unnecessary sort and re-calculation of sum.
        Self { vars, sum }
    }

    #[inline]
    fn sum(&self) -> u32 {
        self.sum
    }

    #[inline]
    fn var_count(&self) -> usize {
        self.vars.len()
    }

    pub fn vars(&self) -> impl Iterator<Item = &VarIndex> {
        self.vars.iter()
    }
}

impl PartialEq<Self> for Term {
    fn eq(&self, other: &Self) -> bool {
        self.sum() == other.sum() && self.vars == other.vars
    }
}

impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // `sum` is entirely derived from the `vars`, so no need to hash it
        self.vars.hash(state)
    }
}

impl Ord for Term {
    fn cmp(&self, other: &Self) -> Ordering {
        let self_sum = self.sum();
        let other_sum = other.sum();
        if self_sum != other_sum {
            return self_sum.cmp(&other_sum);
        }
        if self.var_count() != other.var_count() {
            return self.var_count().cmp(&other.var_count());
        }
        for (s, o) in self.vars.iter().zip(other.vars.iter()) {
            if s != o {
                return s.cmp(o);
            }
        }
        Ordering::Equal
    }
}

impl PartialOrd<Self> for Term {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl From<Vec<VarIndex>> for Term {
    fn from(v: Vec<VarIndex>) -> Self {
        Self::new(v)
    }
}

impl From<VarIndex> for Term {
    fn from(v: VarIndex) -> Self {
        Self::new(vec![v])
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (ii, v) in self.vars.iter().enumerate() {
            let is_first = ii == 0;
            if is_first {
                write!(f, "{v}")?;
            } else {
                write!(f, "*{v}")?;
            }
        }
        Ok(())
    }
}

impl<C: Coef> FromStr for Polynom<C> {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let m = C::MAX_MOD;
        let p = Self::from_monoms(
            m,
            crate::parse_poly(s.as_bytes()).map(|(c, t)| (C::from_big(&c, m), t.into())),
        );
        Ok(p)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coef::ArrayCoef;

    #[test]
    fn test_term() {
        // normalize order when creating term
        let t1 = Term::new(vec![1.into(), 2.into()]);
        assert_eq!(format!("{t1}"), "x1*x2");
        let t2 = Term::new(vec![2.into(), 1.into()]);
        assert_eq!(format!("{t2}"), "x1*x2");
        assert_eq!(t1, t2);
        let one = Term::new(vec![]);
        assert_eq!(format!("{one}"), "");
    }

    #[test]
    fn test_poly() {
        let m = ArrayCoef::<1>::MAX_MOD;
        let p = Polynom::from_monoms(
            m,
            vec![(ArrayCoef::<1>::from_i64(1, m), vec![].into())].into_iter(),
        );
        assert_eq!(format!("{p}"), "[1*]");
    }

    #[test]
    fn test_substitution() {
        // let's start with just the monomial that will be replaced: [2*x2818]
        let m = Mod::from_bits(32);
        let mut p = Polynom::from_monoms(
            m,
            vec![(ArrayCoef::<1>::from_i64(2, m), vec![2818.into()].into())].into_iter(),
        );
        assert_eq!(format!("{p}"), "[2*x2818]");

        // small example from benchmark 01: -1*x2818-1*x38+1
        let mons = vec![
            (Coef::from_i64(-1, m), vec![38.into()].into()),
            (Coef::from_i64(1, m), vec![].into()),
        ];
        p.replace_var(2818.into(), &mons);
        assert_eq!(p.size(), 2);
        assert_eq!(format!("{p}"), "[2*] + [4294967294*x38]");

        // there used to be a substitution bug where the old variable would not be
        // removed if the index was less than the index of the new variable
        let mons = vec![(Coef::from_i64(-1, m), vec![2818.into()].into())];
        p.replace_var(38.into(), &mons);
        assert_eq!(p.size(), 2);
        assert_eq!(format!("{p}"), "[2*] + [2*x2818]");
    }

    #[test]
    fn test_add() {
        let m = Mod::from_bits(8);
        let mut a = Polynom::<u64>::from_str("2*x1 - 2*x2").unwrap();
        a.m = m;
        let mut b = Polynom::<u64>::from_str("254*x1 + 2*x2 + 2*x3").unwrap();
        b.m = m;
        a.add_assign(&b);
        assert_eq!(format!("{a}"), "[2*x3]");
    }

    #[test]
    fn test_mul() {
        let m = Mod::from_bits(8);
        let mut a = Polynom::<u64>::from_str("2*x1 - 2*x2").unwrap();
        a.m = m;
        let mut b = Polynom::<u64>::from_str("254*x1 + 2*x2 + 2*x3").unwrap();
        b.m = m;
        let r = a.mul(&b);
        assert_eq!(
            format!("{r}"),
            "[252*x1] + [252*x2] + [8*x1*x2] + [4*x1*x3] + [252*x2*x3]"
        );
    }

    #[test]
    fn test_coef_sum() {
        assert_eq!(
            Polynom::<u64>::from_str("2*x1 - 2*x2").unwrap().coef_sum(),
            0
        );
    }

    #[test]
    fn test_scale() {
        let mut a = Polynom::<u64>::from_str("2*x1 - 2*x2").unwrap();
        a.m = Mod::from_bits(8);
        a.scale(&3);
        assert_eq!(format!("{a}"), "[6*x1] + [250*x2]");
    }
}
