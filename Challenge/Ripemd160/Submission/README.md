# RIPEMD-160 bytecode candidate

This directory provides the exact bytecode and Lean candidate theorem for the
benchmark's RIPEMD-160 contract.

## Artifact

- Byte length: 5,268
- Decoded instructions: 3,167
- Hex-file SHA-256: `498bea19bf2dffe508587a9eb979b3327cb2262da29da14b5f69483c778ceffe`
- Raw-byte SHA-256: `6687bf3ba061e8c417993791b842de4054c585b93e5816fc44b76ff163f5ec91`
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
