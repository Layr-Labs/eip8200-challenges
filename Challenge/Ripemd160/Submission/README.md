# RIPEMD-160 bytecode candidate

This directory provides the exact bytecode and Lean candidate theorem for the
benchmark's RIPEMD-160 contract.

## Artifact

- Byte length: 5,268
- Decoded instructions: 3,167
- Hex-file SHA-256: `afeeefb5f795b6e3f91f52fe41efee8449df9469ca523718a8537db72b4e60e1`
- Raw-byte SHA-256: `a53d5be608ad6e18641c259c2ce8827e82e8cd0cd9e82cf51f0418bc9fc5c597`
- Official evaluation and promotion status: recorded separately by the platform.

## Verification contract

`Solution.lean` exports `Challenge.Ripemd160.Benchmark.candidate` with the exact
required type `Challenge.Ripemd160.Correct bytecode`. This statement covers
every calldata satisfying `CalldataFits` and every sufficiently large gas
budget, not only the measured vectors. The required result is twelve zero
bytes followed by the twenty-byte RIPEMD-160 digest.

The standard benchmark independently binds the theorem to `bytecode.hex`,
checks its transitive axiom footprint, and scores only protected verified
bytes. Native gas measurements are testing evidence, not a correctness proof.
The permitted axiom set is `propext`, `Classical.choice`, and `Quot.sound`.

The instruction at PC 4967 is now POP: it consumes the former jump target
and falls through to PC 4968, saving six gas with identical resulting state.
Run `node check/artifact.mjs` to check all byte representations and run
`cd check && forge test -vv` for native digest and exact gas regression checks.
