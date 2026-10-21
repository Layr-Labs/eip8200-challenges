# RIPEMD-160: inline the size-32 schedule constant

Runtime: **9,742 bytes**, 5,448 decoded instructions. Hex-file SHA-256:
`28c40a43d1732ccc9ad275a81780020cd8472ce28147f02ce5a3b3d7dda3890a`.
Decoded-runtime SHA-256:
`a8dbdd40c63c402be33bcc664e1f96b6ff2631d791ec8fc1a94bdd40369ff3a3`.

Direct baseline: accepted/promoted `fc49bf69-df48-433e-8a6f-73c38f7bcc18`,
official 639,953 gas, promoted source `973453b56d2c4d04006f3e8c42ff296a6c5e9cb3`.

## Runtime transformation

The guard at PCs 151..187 writes the same 32-byte schedule constant at memory
162 with `PUSH29; PUSH1 162; MSTORE; PUSH2 497; JUMPI`, replacing its old
CODECOPY argument setup. The existing active-memory invariant prevents expansion.
This saves 5 gas on each of the 11 generated 32-byte vectors.

The guard's zero-flag path takes `PUSH2 9715; JUMP` at PCs 188..191. The old
cold padding fragment [165,192) is copied verbatim to [9715,9742). This cold
trampoline costs 11 extra gas when taken; no scored default vector takes it.
Only 38 original bytes in [151,192) change; all other original bytes remain fixed.
The general RIPEMD compressor, content checks, output and arbitrary-input fallback
are retained.

## Proof and measurement

`Shared32SparseRun` proves the exact store and both flag branches;
`Shared32Trace` installs its located GasSteps. Artifact literals and physical PC
witnesses are migrated, including the parallel retained-terminal proof copy.
`BytecodeBinding.exact` uses `rfl`, not native_decide. The universal public endpoint
is still `Challenge.Ripemd160.Benchmark.candidate`.

The isolated existing project entry points passed on 2026-10-21:

- `lake build Challenge.Ripemd160.Submission.Solution`: all 3,791 jobs succeed;
  theorem axioms only propext, Classical.choice, Quot.sound.
- `./benchmark.sh ripemd160`: protected Linux sandbox; Lean default kernel accepts;
  Comparator accepted; **639,898 gas**, 49 vectors, clean=dirty,
  stateIndependentGas=true. The protected byte file matches this submission.

A separate nonauthoritative differential EVM screen over 11 corpus seeds retained
-55 gas for every seed, with no digest or clean/dirty mismatches. These screens
are not the proof and do not determine any undisclosed evaluator seed.

Reproduce from the repository root using `./setup.sh ripemd160` if needed, then
`./benchmark.sh ripemd160`. Lean toolchain: 4.31.0. Official platform evaluation
and promotion remain separate from the protected local result.

## Provenance

`dependencies.json` preserves material inherited sources and explicitly declares
the accepted direct baseline. The old no-code-used 2cc229ec comparison record is
omitted to fit the platform's 20-entry limit. No code from rejected df0a826a was
used. Final verification/packaging route: configured gpt-6-luna, angelX, high effort.
