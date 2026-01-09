// Copyright 2025-2026 Cornell University
// released under MIT license
// author: Kevin Laeufer <laeufer@cornell.edu>

use clap::Parser;
use polysub::*;

#[derive(Parser, Debug)]
#[command(name = "bench")]
#[command(version)]
#[command(about = "Performs variable substitutions from a fast-poly benchmark file.", long_about = None)]
struct Args {
    #[arg(long, help = "Print the step number and polysize.")]
    print_step: bool,
    #[arg(long, help = "Print the polynom after every step.")]
    print_poly: bool,
    #[arg(long)]
    max_steps: Option<u32>,
    #[arg(value_name = "BENCHMARK", index = 1)]
    filename: String,
}

/// 8 * 64 bit = 512 bit which is enough for benchmarks involving 256 bit multipliers.
type DefaultCoef = ArrayCoef<8>;

fn main() {
    let args = Args::parse();
    let content = std::fs::read_to_string(args.filename).expect("failed to read benchmark file");
    let (poly, max_poly_size) = exec_benchmark::<DefaultCoef>(
        content.as_bytes(),
        args.max_steps,
        args.print_step,
        args.print_poly,
    );
    println!("Max. Size was {}", max_poly_size);
    println!("{}", poly);
}
