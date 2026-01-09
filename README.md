# polysub

A library for fast variable substitution for polynomials.

Uses the `refList` optimization invented by the [fastpoly library](https://github.com/a-konrad/fastpoly/) and many additional optimizations.


## Benchmarks

We used the benchmarks from the FastPoly paper, Table 1.
`polysub` is roughly 10x faster than FastPoly on every benchmark, except for `8-bit sp-ar-ks`.

|        Benchmark | # steps | start size | `polysub` | FastPoly | max size |
|-----------------:|--------:|-----------:|----------:|---------:|---------:|
|  16-bit sp-ar-rc |   2,816 |        288 |    0.003s |   0.029s |      302 |
|  32-bit sp-ar-rc |  11,776 |      1,088 |    0.011s |   0.122s |    1,102 |
|  64-bit sp-ar-rc |  48,128 |      4,224 |    0.049s |   0.501s |    4,298 |
| 128-bit sp-ar-rc | 194,560 |     16,640 |    0.195s |   2.003s |   16,654 |
| 256-bit sp-ar-rc | 782,336 |     66,048 |    0.796s |   8.337s |   66,062 |
|  16-bit sp-wt-lf |   3,057 |        288 |    0.005s |   0.036s |      670 |
|  32-bit sp-wt-lf |  12,616 |      1,088 |    0.016s |   0.146s |    2,055 |
|  64-bit sp-wt-lf |  50,564 |      4,224 |    0.066s |   0.579s |    8,315 |
| 128-bit sp-wt-lf | 200,100 |     16,640 |    0.253s |   2.345s |   26,522 |
| 256-bit sp-wt-lf | 796,191 |     66,048 |    1.341s |  10.485s |   82,154 |
|   8-bit sp-ar-ks |     652 |         80 |    0.212s |   0.531s |   54,473 |

**Note**: the _max size_ is different from what is reported in the FMCAD'25 paper.
We report the number calculated by both, the version of FastPoly we benchmarked and our own `polysub`. 


### Benchmarking Details

- All benchmarks were ran on a machine running Fedora Linux 43 with a `AMD Ryzen 9 9950X` processor and 64 GiB of main memory.
- We used `polysub` commit `aa16664d39a7a005c792010876f4ad06e4ef8731`.
- We compiled `polysub` with `rustc 1.92.0`: `cargo build --examples --release`.
- We benchmarked with `hyperfine`: `hyperfine -N "./target/release/examples/bench $BENCHMARK"`.
- For the faster benchmarks, we observed some warmup effects from the benchmark file getting cached.
- We used FastPoly commit `480669d7de96ce6f794b1b49c9eb0e24a922e1aa`.
- We modified the `fastpoly_demo.cpp` to use `argv[1]` as argument to `init_spec` and `reduce_poly` and deleted the rest of the demo.
- We compiled FastPoly with `g++ (GCC) 15.2.1`: `g++ src/* -Wall -Wextra -std=c++11 -O3 -DNDEBUG -DHAVEGETRUSAGE -DHAVEUNLOCKEDIO -lgmp -lgmpxx -o fastpoly`
- We benchmarked FastPoly like this: `hyperfine -N "./fastpoly $BENCHMARK"`


Benchmark source:

```
Konrad, Alexander, and Christoph Scholl.
"FastPoly: An Efficient Polynomial Package for the Verification of Integer Arithmetic Circuits."
In CONFERENCE ON FORMAL METHODS IN COMPUTER-AIDED DESIGN–FMCAD 2025, p. 139. 2025.
```

## Impact of Coefficient Implementation

`polysub` makes heavy use of the fact, that all benchmarks use modulo arithmetic for their coefficients.
The `Coef` trait makes it simple to switch out the coefficient implementation. We performed all benchmarks above
with a 512-bit coefficient implementation. However, we can use smaller coefficient implementations for the less
wide benchmarks. By switching the `DefaultCoef` in `examples/bench.rs` to `u64`, we improve the runtime on `8-bit sp-ar-ks`
to 164ms, for a 30% improvement. This shows that -- unfortunately -- the coefficient size is not super important for the performance.