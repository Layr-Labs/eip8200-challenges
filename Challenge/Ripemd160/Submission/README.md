# RIPEMD-160 bytecode candidate

This directory provides the exact bytecode and Lean candidate theorem for the
benchmark's RIPEMD-160 contract.

## Artifact

- Byte length: 5,268
- Decoded instructions: 3,167
- Hex-file SHA-256: `32cdef0d9da0ddab52b7d542ca56a0449e5c578d864d4c7e12e6d271d4181e16`
- Raw-byte SHA-256: `a31d892161f740c794b216163206dac64eebd5396e1a20a3b711412ce62f424b`
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
