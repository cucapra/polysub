// Copyright 2025-2026 Cornell University
// released under MIT license
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::Parser;
use num_bigint::BigInt;
use polysub::*;
use regex::Regex;
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::LazyLock;

#[derive(Parser, Debug)]
#[command(name = "diff")]
#[command(version)]
#[command(about = "Diffs the output of two substitution runs", long_about = None)]
struct Args {
    #[arg(short, long)]
    verbose: bool,
    #[arg(long)]
    max_steps: Option<u32>,
    #[arg(value_name = "A", index = 1)]
    a: String,
    #[arg(value_name = "B", index = 2)]
    b: String,
}

#[derive(Debug, PartialEq)]
enum LineContent {
    CurrentStep(usize, u32),
    Polynom(Vec<(BigInt, Term)>),
}

static CURRENT_STEP_RE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"Current step: (\d+) with poly\.size: (\d+)").unwrap());

fn parse_line(line: &str) -> LineContent {
    let line = line.trim();
    if let Some(current_step) = CURRENT_STEP_RE.captures(line) {
        let step: usize = current_step[1].parse().unwrap();
        let poly_size: u32 = current_step[2].parse().unwrap();
        LineContent::CurrentStep(step, poly_size)
    } else if line.starts_with('[') {
        let poly: Vec<_> = parse_poly(line.as_bytes())
            .map(|(coef, vars)| (coef, vars.into()))
            .collect();
        LineContent::Polynom(poly)
    } else {
        todo!("{line}")
    }
}

fn analyze_poly_diff(step: usize, a: &[(BigInt, Term)], b: &[(BigInt, Term)]) {
    let a_map = FxHashMap::from_iter(a.iter().map(|(coef, vars)| (vars.clone(), coef.clone())));
    let b_map = FxHashMap::from_iter(b.iter().map(|(coef, vars)| (vars.clone(), coef.clone())));
    let mut common: Vec<_> = FxHashSet::from_iter(a_map.keys())
        .intersection(&FxHashSet::from_iter(b_map.keys()))
        .cloned()
        .cloned()
        .collect();
    common.sort();
    for term in common.iter() {
        let a_coef = &a_map[term];
        let b_coef = &b_map[term];
        if a_coef != b_coef {
            println!("STEP {step}: Coef: {a_coef} vs {b_coef} for {term}");
        }
    }
    for (coef, term) in a.iter() {
        if !b_map.contains_key(term) {
            println!("STEP {step}: Only in A: {coef} * {term}");
        }
    }
    for (coef, term) in b.iter() {
        if !a_map.contains_key(term) {
            println!("STEP {step}: Only in B: {coef} * {term}");
        }
    }
}

fn analyze_diff(last_step: usize, a: &LineContent, b: &LineContent) -> usize {
    match (a, b) {
        (LineContent::CurrentStep(a_step, a_size), LineContent::CurrentStep(b_step, b_size)) => {
            if a_step != b_step {
                println!("Step number is different (did you skip a step?): {a_step} != {b_step}");
                last_step
            } else if a_size != b_size {
                println!("STEP {a_step}: {a_size} != {b_size}");
                *a_step
            } else {
                unreachable!()
            }
        }
        (LineContent::Polynom(poly_a), LineContent::Polynom(poly_b)) => {
            analyze_poly_diff(last_step, poly_a, poly_b);
            last_step
        }
        (_, _) => {
            debug_assert_ne!(line_content_name(a), line_content_name(b));
            println!(
                "Different line types: {} vs {}",
                line_content_name(a),
                line_content_name(b)
            );
            last_step
        }
    }
}

fn line_content_name(c: &LineContent) -> &'static str {
    match c {
        LineContent::CurrentStep(_, _) => "current step",
        LineContent::Polynom(_) => "polynom",
    }
}

fn main() {
    let args = Args::parse();
    let a_content = std::fs::read_to_string(&args.a).expect("failed to read file A");
    let b_content = std::fs::read_to_string(&args.b).expect("failed to read file B");
    let a_line_count = a_content.lines().count();
    let b_line_count = b_content.lines().count();
    if a_line_count > b_line_count {
        println!(
            "WARN: {} lines in {} will be ignored",
            a_line_count - b_line_count,
            args.a
        );
    }
    if b_line_count > a_line_count {
        println!(
            "WARN: {} lines in {} will be ignored",
            b_line_count - a_line_count,
            args.b
        );
    }
    let mut last_step = 0;
    for (a_line, b_line) in a_content.lines().zip(b_content.lines()) {
        let a_content = parse_line(a_line);
        let b_content = parse_line(b_line);
        if a_content != b_content {
            last_step = analyze_diff(last_step, &a_content, &b_content);
        } else if let LineContent::CurrentStep(step, _) = a_content {
            println!("STEP {step}");
            last_step = step;
        }
    }
}
