// Copyright 2025-2026 Cornell University
// released under MIT license
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{Term, VarIndex};
use std::num::NonZeroU32;

/// Maintains one list for each variable with the terms that contain it.
/// This data structure is our version of the `refList` suggested by
/// Alexander Konrad and Christoph Scholl in their FastPoly paper (FMCAD'25).
#[derive(Debug)]
pub struct VarMap {
    /// Keep track of the list entries that refer to a given term.
    terms: Vec<TermMeta>,
    /// First entry of the list for a given VarIndex.
    heads: Vec<Option<EntryId>>,
    /// List entries.
    entries: Vec<Entry>,
    /// Keeps track of freed entries.
    free: Vec<EntryId>,
}

#[derive(Debug, Clone)]
struct Entry {
    term: TermId,
    next: Option<EntryId>,
    prev: Option<EntryId>,
}

#[derive(Debug, Clone, Default)]
struct TermMeta {
    entries: Vec<EntryId>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct TermId(NonZeroU32);

impl From<usize> for TermId {
    fn from(value: usize) -> Self {
        Self(NonZeroU32::new(value as u32 + 1).unwrap())
    }
}

impl From<TermId> for usize {
    fn from(value: TermId) -> Self {
        value.0.get() as usize - 1
    }
}

#[derive(Debug, Clone, Copy)]
struct EntryId(NonZeroU32);

impl From<usize> for EntryId {
    fn from(value: usize) -> Self {
        Self(NonZeroU32::new(value as u32 + 1).unwrap())
    }
}

impl From<EntryId> for usize {
    fn from(value: EntryId) -> Self {
        (value.0.get() - 1) as usize
    }
}

impl VarMap {
    pub fn new() -> Self {
        Self {
            terms: vec![],
            heads: vec![],
            entries: vec![],
            free: vec![],
        }
    }

    /// add a new unique! term
    pub fn add_term(&mut self, term: &Term, term_id: TermId) {
        // make sure there is space for term metadata
        let term_index: usize = term_id.into();
        if self.terms.len() <= term_index {
            self.terms.resize(term_index + 1, TermMeta::default());
        }
        debug_assert!(self.terms[term_index].entries.is_empty());

        // insert term into list and also add back pointer
        for &var in term.vars() {
            let new_entry = self.add_list_entry(var, term_id);
            self.terms[term_index].entries.push(new_entry);
        }
    }

    pub fn remove_term(&mut self, term: &Term, term_id: TermId) {
        let term_index: usize = term_id.into();
        debug_assert!(self.terms.len() > term_index, "term entry not found!");

        // remove all entries that refer to this term
        for (entry_id, &var_id) in self.terms[term_index].entries.drain(..).zip(term.vars()) {
            let entry_index: usize = entry_id.into();
            let entry_prev = self.entries[entry_index].prev;
            let entry_next = self.entries[entry_index].next;

            // fix the next pointer of the previous entry
            if let Some(prev_id) = entry_prev {
                // change previous entry
                let prev_index: usize = prev_id.into();
                self.entries[prev_index].next = entry_next;
            } else {
                // if this is the first element in the list, we need to change the list head
                let var_index: usize = var_id.into();
                self.heads[var_index] = entry_next;
            }

            // fix the prev pointer of the next entry
            if let Some(next_id) = entry_next {
                let next_index: usize = next_id.into();
                self.entries[next_index].prev = entry_prev;
            }

            // the entry is now unused, since each entry is only ever used in a single list
            self.free.push(entry_id);
        }
    }

    pub fn terms_for_var(&self, var: VarIndex) -> impl Iterator<Item = TermId> {
        let var_index: usize = var.into();
        TermIter {
            lookup: self,
            entry: self.heads[var_index],
        }
    }

    /// Adds a new list entry to the front of the list for the particular variable and returns
    /// the id of the new entry.
    fn add_list_entry(&mut self, var_id: VarIndex, term: TermId) -> EntryId {
        let var_index: usize = var_id.into();
        // make sure there is enough space in our `heads` vector
        // this is necessary because we do not know the biggest VarIndex ahead of time
        if var_index >= self.heads.len() {
            self.heads.resize(var_index + 1, None);
        }
        // we always insert at the front of the list
        let prev = None;
        let next = self.heads[var_index];
        let new_entry_id = self.allocate_entry(term, next, prev);
        self.heads[var_index] = Some(new_entry_id);
        if let Some(old_head_id) = next {
            let old_head_index: usize = old_head_id.into();
            self.entries[old_head_index].prev = Some(new_entry_id);
        }
        new_entry_id
    }

    /// Returns the id of a free entry
    fn allocate_entry(
        &mut self,
        term: TermId,
        next: Option<EntryId>,
        prev: Option<EntryId>,
    ) -> EntryId {
        if let Some(entry) = self.free.pop() {
            let entry_index: usize = entry.into();
            self.entries[entry_index] = Entry { term, next, prev };
            entry
        } else {
            let id = self.entries.len().into();
            self.entries.push(Entry { term, next, prev });
            id
        }
    }
}

struct TermIter<'a> {
    lookup: &'a VarMap,
    entry: Option<EntryId>,
}

impl<'a> Iterator for TermIter<'a> {
    type Item = TermId;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(entry_id) = self.entry {
            let entry_index: usize = entry_id.into();
            let entry = &self.lookup.entries[entry_index];
            self.entry = entry.next;
            Some(entry.term)
        } else {
            None
        }
    }
}
