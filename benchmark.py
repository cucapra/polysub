#!/usr/bin/env python3
# benchmarking script generated with CopilotAI

import multiprocessing
import subprocess
import concurrent.futures
import json
import tempfile
import os
import math
import glob
import itertools
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
BENCHMARKS = glob.glob(f"{SCRIPT_DIR}/benchmarks/*_steps")
MAX_WORKERS = max(1, multiprocessing.cpu_count() // 2)
FLAGS = [("", "", set()), ("(PO)", "--phase-opt", {"b04", "b05", "b09", "b10"})]


def run_hyperfine(name: str, benchmark: str, flags: str):
    with tempfile.NamedTemporaryFile(delete=True, suffix=".json") as tmp:
        json_path = tmp.name

        hf_cmd = [
            "hyperfine",
            "--warmup",
            "2",
            "-N",
            "--export-json",
            json_path,
            f"./target/release/examples/bench {benchmark} {flags}",
        ]

        result = subprocess.run(hf_cmd, capture_output=True, text=True, check=False)

        if result.returncode != 0:
            raise RuntimeError(
                f"Hyperfine failed for benchmark '{benchmark}': {result.stderr.strip()}"
            )

        with open(json_path, "r") as f:
            data = json.load(f)

        entry = data["results"][0]
        mean = entry["mean"]
        stddev = entry["stddev"]

        return name, mean, stddev


def main():
    results = []

    # ensure that we have the latest version built
    subprocess.run(
        ["cargo", "build", "--release", "--examples"],
        cwd=SCRIPT_DIR,
        stdout=subprocess.PIPE,
        check=True,
        shell=False,
    )

    # generate all runs
    runs = [
        (f"{Path(bb).name} {s}", bb, f)
        for bb, (s, f, skip) in itertools.product(BENCHMARKS, FLAGS)
        if Path(bb).name[:3] not in skip
    ]

    with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = [executor.submit(run_hyperfine, *args) for args in runs]

        for future in concurrent.futures.as_completed(futures):
            results.append(future.result())

    # Print table header
    print(f"{'BENCHMARK':<60} {'MEAN (s)':>12} {'STDDEV':>12}")
    print("-" * 82)

    # sort by benchmark name
    results.sort(key=lambda e: e[0])

    # Print table rows
    for bb, mean, stddev in results:
        print(f"{bb:<60} {mean:>12.6f} {stddev:>12.6f} ")


if __name__ == "__main__":
    main()
