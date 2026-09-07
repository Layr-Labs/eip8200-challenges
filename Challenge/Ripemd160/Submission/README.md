# RIPEMD-160 bytecode candidate

This directory provides the exact bytecode and Lean candidate theorem for the
benchmark's RIPEMD-160 contract.

## Artifact

- Byte length: 5,305
- Decoded instructions: 3,234
- Hex-file SHA-256: `baf10ee2c322a41696ff7a745aedb7293ca0dd179e9854ce30165b1188461a95`
- Raw-byte SHA-256: `facbc97e2beb7a825cd15ac3ed49271a0dc5f5994821a275e77684e42b9276c6`
- Native 49-vector clean gas total: 1,575,468
- Native 49-vector dirty gas total: 1,575,468
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
