#!/usr/bin/env bash
# Run from the challenge repository root after ./setup.sh ripemd160.
set -euo pipefail
python3 scripts/yukon_benchmark.py prepare ripemd160 \
  Challenge/Ripemd160/Submission/bytecode.hex \
  benchmark-results/ripemd160/verified-bytecode.hex \
  Challenge/Ripemd160/Benchmark/Artifact.lean \
  Challenge/Ripemd160/Benchmark/Challenge.lean
./scripts/build-lean-serial.sh Challenge.Ripemd160.Submission.Solution
BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh ripemd160
