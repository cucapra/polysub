// Copyright 2025-2026 Cornell University
// released under MIT license
// author: Kevin Laeufer <laeufer@cornell.edu>

mod benchmark;
mod coef;
mod parser;
mod poly;
mod varmap;

pub use benchmark::exec_benchmark;
pub use coef::{ArrayCoef, Coef, Mod};
pub use parser::parse_poly;
pub use poly::{Polynom, Term, VarIndex};
