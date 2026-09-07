# RIPEMD-160 bytecode candidate

This directory provides the exact bytecode and Lean candidate theorem for the
benchmark's RIPEMD-160 contract.

## Artifact

| Surface | State |
|---|---|
| Runtime artifact | Updated |
| Byte-array source | Updated |
| Decoded instruction source | Updated |
| Scanner state and execution certificates | Updated |
| Challenge-owned interfaces | Preserved |

The public parent is terrapinelf's RIPEMD-160 submission in pull request 564.
This package also restores part of i34-9's earlier accepted contribution.
Official validation and promotion status belong to the platform record.

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
