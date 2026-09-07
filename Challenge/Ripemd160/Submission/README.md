# RIPEMD-160 bytecode candidate

This directory provides the exact bytecode and Lean candidate theorem for the
benchmark's RIPEMD-160 contract.

## Artifact

- Byte length: 5,256
- Decoded instructions: 3,155
- Hex-file SHA-256: `52abdc32054c60af07914ba762d4cf1a53787b126c45dd70a74f0ce7ca78e126`
- Raw-byte SHA-256: `9f89bd18331ae362abffeaf035a7e2d821fd1e2665606890a831a5d1fb28aa6c`
- Native 49-vector clean gas total: 1,530,785
- Native 49-vector dirty gas total: 1,530,785
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
