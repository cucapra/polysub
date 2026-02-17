// Copyright 2025-2026 Cornell University
// released under MIT license
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::{Coef, Mod, Polynom, parse_poly};
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
) -> (Polynom<C>, usize) {
    let mut line_count = 0u32;
    let mut max_poly_size = 0;
    let mut poly: Option<Polynom<C>> = None;
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
                let p = Polynom::from_monoms(
                    m,
                    parse_poly(line.as_bytes()).map(|(c, t)| (c.into_coef(m), t.into())),
                );
                max_poly_size = p.size();
                poly = Some(p);
            }
            line_nr => {
                // early exit
                let step_nr = line_nr - 2;
                if let Some(max_steps) = max_steps
                    && step_nr > max_steps
                {
                    return (poly.unwrap(), max_poly_size);
                }

                // parse line
                let mut monom_iter = parse_poly(line.as_bytes());
                let (first_coef, sub_var) = monom_iter.next().unwrap();
                assert_eq!(first_coef.as_i64(), Some(-1));
                assert_eq!(sub_var.len(), 1);
                let sub_var = sub_var[0];
                let poly = poly.as_mut().unwrap();
                poly.replace_var(
                    sub_var,
                    &monom_iter
                        .map(|(c, t)| (c.into_coef(m), t.into()))
                        .collect::<Vec<_>>(),
                );
                max_poly_size = std::cmp::max(max_poly_size, poly.size());
                if print_step {
                    println!("Current step: {step_nr} with poly.size: {}", poly.size());
                }
                if print_poly {
                    println!("{}", poly);
                }
            }
        }
        line_count += 1;
    }
    (poly.unwrap(), max_poly_size)
}
