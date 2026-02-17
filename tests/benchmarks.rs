// Copyright 2025-2026 Cornell University
// released under MIT license
// author: Kevin Laeufer <laeufer@cornell.edu>

use polysub::*;

type DefaultCoef = ArrayCoef<8>;

#[test]
fn full_adder_example() {
    let inp = b"\
            8
            0
            +2*x8+1*x7
            -1*x8-1*x5*x6+1*x5+1*x6
            -1*x6+1*x3*x4
            -1*x7-2*x3*x4+1*x3+1*x4
            -1*x5+1*x1*x2
            -1*x4-2*x1*x2+1*x1+1*x2
        ";
    let (poly, _max_poly_size) = exec_benchmark::<DefaultCoef>(inp, None, true, false, false);
    assert_eq!(format!("{}", poly), "[1*x1] + [1*x2] + [1*x3]");
}

fn test_benchmark(
    filename: &str,
    expected_max_poly_size: usize,
    max_steps: Option<u32>,
    phase_opt: bool,
) {
    let content = std::fs::read_to_string(filename).expect("failed to read benchmark file");
    let (poly, max_poly_size) =
        exec_benchmark::<DefaultCoef>(content.as_bytes(), max_steps, false, false, phase_opt);
    assert!(
        poly.is_zero(),
        "Result should be an zero polynomial. Instead we get: {}",
        poly
    );
    assert_eq!(max_poly_size, expected_max_poly_size);
}

#[test]
fn test_b01() {
    test_benchmark("benchmarks/b01_sp-ar-rc_16bit_steps", 302, None, false);
}

#[test]
fn test_b01_phase_opt() {
    test_benchmark("benchmarks/b01_sp-ar-rc_16bit_steps", 294, None, true);
}

#[test]
fn test_b02() {
    test_benchmark("benchmarks/b02_sp-ar-rc_32bit_steps", 1_102, None, false);
}

#[test]
fn test_b02_phase_opt() {
    test_benchmark("benchmarks/b02_sp-ar-rc_32bit_steps", 1_094, None, true);
}

#[test]
fn test_b03() {
    test_benchmark("benchmarks/b03_sp-ar-rc_64bit_steps", 4_298, None, false);
}

#[test]
fn test_b03_phase_opt() {
    test_benchmark("benchmarks/b03_sp-ar-rc_64bit_steps", 4_292, None, true);
}

#[test]
fn test_b04() {
    // the paper reports 16,640 as the max size which does not agree with what fastpoly reports
    // 194,560 steps, 38.77s
    test_benchmark("benchmarks/b04_sp-ar-rc_128bit_steps", 16_654, None, false);
}

#[test]
fn test_b04_phase_opt() {
    test_benchmark("benchmarks/b04_sp-ar-rc_128bit_steps", 16_646, None, true);
}

#[test]
fn test_b05() {
    // the paper reports 66,048 as the max size which does not agree with what fastpoly reports
    // 782,336 steps, 150.35s
    test_benchmark("benchmarks/b05_sp-ar-rc_256bit_steps", 66_062, None, false);
}

#[ignore] // TODO: make faster
#[test]
fn test_b05_phase_opt() {
    test_benchmark("benchmarks/b05_sp-ar-rc_256bit_steps", 66_062, None, true);
}

#[test]
fn test_b06() {
    // the paper reports 288 as the max size which does not agree with what fastpoly reports
    test_benchmark("benchmarks/b06_sp-wt-lf_16bit_steps", 670, None, false);
}

#[test]
fn test_b06_phase_opt() {
    test_benchmark("benchmarks/b06_sp-wt-lf_16bit_steps", 446, None, true);
}

#[test]
fn test_b07() {
    // the paper reports 1,088 as the max size which does not agree with what fastpoly reports
    test_benchmark("benchmarks/b07_sp-wt-lf_32bit_steps", 2_055, None, false);
}

#[test]
fn test_b07_phase_opt() {
    test_benchmark("benchmarks/b07_sp-wt-lf_32bit_steps", 1_511, None, true);
}

#[test]
fn test_b08() {
    // the paper reports 4,224 as the max size which does not agree with what fastpoly reports
    // 50,564 steps, 9.84s
    test_benchmark("benchmarks/b08_sp-wt-lf_64bit_steps", 8_315, None, false);
}

#[test]
fn test_b08_phase_opt() {
    test_benchmark("benchmarks/b08_sp-wt-lf_64bit_steps", 5_421, None, true);
}

#[test]
fn test_b09() {
    // the paper reports 16,640 as the max size which does not agree with what fastpoly reports
    // 200,100 steps, 38.65s
    test_benchmark("benchmarks/b09_sp-wt-lf_128bit_steps", 26_522, None, false);
}

#[test]
fn test_b09_phase_opt() {
    test_benchmark("benchmarks/b09_sp-wt-lf_128bit_steps", 19_626, None, true);
}

#[test]
fn test_b10() {
    // the paper reports 66,048 as the max size which does not agree with what fastpoly reports
    // 796,191 steps, 158.00s
    test_benchmark("benchmarks/b10_sp-wt-lf_256bit_steps", 82_154, None, false);
}

#[ignore] // TODO: make faster
#[test]
fn test_b10_phase_opt() {
    test_benchmark("benchmarks/b10_sp-wt-lf_256bit_steps", 82_154, None, true);
}

#[test]
fn test_b11() {
    test_benchmark("benchmarks/b11_sp-ar-ks_8bit_steps", 54_473, None, false);
}

#[test]
fn test_b11_phase_opt() {
    test_benchmark("benchmarks/b11_sp-ar-ks_8bit_steps", 1852, None, true);
}
