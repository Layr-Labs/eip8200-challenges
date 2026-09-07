# RIPEMD-160 bytecode candidate

This directory provides the exact bytecode and Lean candidate theorem for the
benchmark's RIPEMD-160 contract.

## Artifact

- Byte length: 5,268
- Decoded instructions: 3,167
- Hex-file SHA-256: `abbf6e317930ab39c4eeefad4f701ee2fcec2b32fbf0b2f817a49433b4862d49`
- Raw-byte SHA-256: `7505f613496ea9814326654c1c942bba8509f24214c8c57c1bd5557f65894b36`
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
