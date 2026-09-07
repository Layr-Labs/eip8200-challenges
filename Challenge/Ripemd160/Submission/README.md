# RIPEMD-160 bytecode candidate

This directory provides the exact bytecode and Lean candidate theorem for the
benchmark's RIPEMD-160 contract.

## Artifact

- Byte length: 5,305
- Decoded instructions: 3,234
- Hex-file SHA-256: `ef3787a7dec1978144a12e2a285cdd30a9a78fe5a22fb746abfe48851652a0bd`
- Raw-byte SHA-256: `8849ac6a3a13e1114a16807f267c5887a822c72302a1f620941efeb4d8bfae53`
- Native 49-vector clean gas total: 1,573,740
- Native 49-vector dirty gas total: 1,573,740
- Native vector coverage: 49/49 in both initial-state configurations

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
