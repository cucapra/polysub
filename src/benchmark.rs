// Copyright 2025-2026 Cornell University
// released under MIT license
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{Coef, Mod, PhaseOptPolynom, Polynom, VarIndex, parse_poly};
use num_bigint::BigUint;
use num_traits::Num;
use std::fmt::Display;
use std::io::BufRead;

/// Execute a benchmark in the format used by the FastPoly paper (FMCAD'25)
pub fn exec_benchmark<C: Coef + Display>(
    content: &[u8],
    max_steps: Option<u32>,
    print_step: bool,
    print_poly: bool,
    phase_opt: bool,
) -> (Polynom<C>, usize) {
    let mut line_count = 0u32;
    let mut max_poly_size = 0;
    let mut poly: Option<Polynom<C>> = None;
    let mut opt_poly: Option<PhaseOptPolynom<C>> = None;
    let mut m = C::MAX_MOD;

    for line in content.lines() {
        let full_line = line.unwrap();
        let line = full_line.trim();
        if line.is_empty() {
            continue;
        }
        match line_count {
            0 => {
                // we are skipping the max var index
                let _max_var_index = line.parse::<u32>().unwrap();
            }
            1 => {
                let coef = BigUint::from_str_radix(line, 10).unwrap();
                if coef != 0u32.into() {
                    m = Mod::from_factor(&coef);
                }
            }
            2 => {
                if phase_opt {
                    let p = PhaseOptPolynom::from_monoms(
                        m,
                        parse_poly(line.as_bytes()).map(|(c, t)| (c.into_coef(m), t.into())),
                    );
                    max_poly_size = p.size();
                    if print_poly {
                        println!("{}", p);
                    }
                    opt_poly = Some(p);
                } else {
                    let p = Polynom::from_monoms(
                        m,
                        parse_poly(line.as_bytes()).map(|(c, t)| (c.into_coef(m), t.into())),
                    );
                    max_poly_size = p.size();
                    if print_poly {
                        println!("{}", p);
                    }
                    poly = Some(p);
                }
            }
            line_nr => {
                // early exit
                let step_nr = line_nr - 2;
                if let Some(max_steps) = max_steps
                    && step_nr > max_steps
                {
                    return if let Some(p) = poly {
                        (p, max_poly_size)
                    } else {
                        (opt_poly.unwrap().into(), max_poly_size)
                    };
                }

                if let Some(p) = poly.as_mut() {
                    // parse line
                    let mut monom_iter = parse_poly(line.as_bytes());
                    let (first_coef, sub_var) = monom_iter.next().unwrap();
                    assert_eq!(first_coef.as_i64(), Some(-1));
                    assert_eq!(sub_var.len(), 1);
                    let sub_var = sub_var[0];

                    // perform replacement
                    p.replace_var(
                        sub_var,
                        &monom_iter
                            .map(|(c, t)| (c.into_coef(m), t.into()))
                            .collect::<Vec<_>>(),
                    );

                    // update and print statistics
                    max_poly_size = std::cmp::max(max_poly_size, p.size());
                    if print_step {
                        println!("Current step: {step_nr} with poly.size: {}", p.size());
                    }
                    if print_poly {
                        println!("{}", p);
                    }
                } else if let Some(p) = opt_poly.as_mut() {
                    // parse line
                    let (var, gate) = Gate::parse(line.as_bytes()).unwrap_or_else(|| {
                        todo!("parse line to gate: {line}");
                    });

                    // perform replacement
                    match gate {
                        Gate::Or(a, b) => p.replace_or(var, a, b),
                        Gate::And(a, b) => p.replace_and(var, a, b),
                        Gate::AndNot(a, b) => p.replace_and_not(var, a, b),
                        Gate::AndNotNot(a, b) => p.replace_and_not_not(var, a, b),
                        Gate::Xor(a, b) => p.replace_xor(var, a, b),
                        Gate::Not(a) => p.replace_not(var, a),
                        Gate::Id(a) => p.replace_identity(var, a),
                        Gate::Input => {} // nothing to do
                    }
                    perform_phase_opt(p, gate);

                    // update and print statistics
                    max_poly_size = std::cmp::max(max_poly_size, p.size());
                    if print_step {
                        println!("Current step: {step_nr} with poly.size: {}", p.size());
                    }
                    if print_poly {
                        println!("{}", p);
                    }
                }
            }
        }
        line_count += 1;
    }
    if let Some(p) = poly {
        (p, max_poly_size)
    } else {
        (opt_poly.unwrap().into(), max_poly_size)
    }
}

fn perform_phase_opt<C: Coef + Display>(p: &mut PhaseOptPolynom<C>, gate: Gate) {
    for var in gate.vars() {
        let prev_size = p.size();
        p.invert(var);
        if p.size() > prev_size {
            p.invert(var);
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum Gate {
    Or(VarIndex, VarIndex),
    And(VarIndex, VarIndex),
    /// a && !b
    AndNot(VarIndex, VarIndex),
    // !a && !b
    AndNotNot(VarIndex, VarIndex),
    Xor(VarIndex, VarIndex),
    Not(VarIndex),
    Id(VarIndex),
    #[allow(dead_code)]
    Input,
}

impl Gate {
    fn parse(line: &[u8]) -> Option<(VarIndex, Self)> {
        let mut monom_iter = parse_poly(line);
        let (first_coef, sub_var) = monom_iter.next().unwrap();
        assert_eq!(first_coef.as_i64(), Some(-1));
        assert_eq!(sub_var.len(), 1);
        let sub_var = sub_var[0];
        let mut poly: Vec<_> = monom_iter.map(|(c, t)| (c.as_i64(), t)).collect();
        poly.sort_by_key(|(_, t)| t.iter().map(|v| u32::from(*v) as u64).sum::<u64>());
        let gate = match poly.as_slice() {
            // identity: a
            [(Some(1), t0)] if t0.len() == 1 => Some(Gate::Id(t0[0])),
            // not: 1 - a
            [(Some(1), t0), (Some(-1), t1)] if t0.is_empty() && t1.len() == 1 => {
                Some(Gate::Not(t1[0]))
            }
            // and: ab
            [(Some(1), t0)] if t0.len() == 2 => Some(Gate::And(t0[0], t0[1])),
            // xor: a + b - 2ab
            [(Some(1), t0), (Some(1), t1), (Some(-2), t2)]
                if t0.len() == 1
                    && t1.len() == 1
                    && t2.len() == 2
                    && t2.contains(&t0[0])
                    && t2.contains(&t1[0]) =>
            {
                Some(Gate::Xor(t0[0], t1[0]))
            }
            // or: a + b - ab
            [(Some(1), t0), (Some(1), t1), (Some(-1), t2)]
                if t0.len() == 1
                    && t1.len() == 1
                    && t2.len() == 2
                    && t2.contains(&t0[0])
                    && t2.contains(&t1[0]) =>
            {
                Some(Gate::Or(t0[0], t1[0]))
            }
            // a && !b: a - ab
            [(Some(1), t0), (Some(-1), t1)]
                if t0.len() == 1 && t1.len() == 2 && t1.contains(&t0[0]) =>
            {
                let a = t0[0];
                let b = *t1.iter().find(|v| **v != a).unwrap();
                Some(Gate::AndNot(a, b))
            }
            // !a && !b: 1 - a - b + ab
            [(Some(1), t0), (Some(-1), t1), (Some(-1), t2), (Some(1), t3)]
                if t0.is_empty()
                    && t1.len() == 1
                    && t2.len() == 1
                    && t3.len() == 2
                    && t1[0] != t2[0]
                    && t3.contains(&t1[0])
                    && t3.contains(&t2[0]) =>
            {
                Some(Gate::AndNotNot(t1[0], t2[0]))
            }
            // unknown pattern
            _ => None,
        };
        gate.map(|g| (sub_var, g))
    }

    fn vars(&self) -> Vec<VarIndex> {
        match self.clone() {
            Gate::Or(a, b) => vec![a, b],
            Gate::And(a, b) => vec![a, b],
            Gate::AndNot(a, b) => vec![a, b],
            Gate::AndNotNot(a, b) => vec![a, b],
            Gate::Xor(a, b) => vec![a, b],
            Gate::Not(a) => vec![a],
            Gate::Id(a) => vec![a],
            Gate::Input => vec![],
        }
    }
}
