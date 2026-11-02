# RIPEMD-160: compact tables, retained operands, and shared execution

The complete correctness theorem and independent Comparator check pass for
this exact image in the challenge's documented local verification mode.
The protected scorer reports **616,801 gas** over 49 default-corpus vectors,
versus **618,026** for public entry `0cb260a1`. All 98 clean/dirty checks pass.
Bytecode size is **10,511 bytes**. Decoded SHA-256:
`ae8b32c6b2ff25a06ed7c300d16ecd6e84b725033fa2b144063802b5f02e87cf`.

The proof base is public commit `7246c880f7b9d96dbf11b1eb533663ae578a3595`.
The candidate combines compact message-table production, retained operands,
a precomputed entry for 32-byte inputs, and joint dispatch and code placement.
Both compressors use ordinary, uncomplemented state at round boundaries.

`Solution.lean` proves `Challenge.Ripemd160.Correct` for the protected literal:
every input shorter than 2^64 bytes returns the specified 32-byte result with
sufficient gas. Its only axioms are `propext`, `Quot.sound`, and `Classical.choice`.

From the challenge repository root:

```sh
./setup.sh ripemd160
bash Challenge/Ripemd160/Submission/verify.sh
```

The verification helper prepares the protected bytecode literal, builds the
solution in dependency order, then runs Comparator and the protected scorer.
It uses the documented non-ranked local mode. Hosted evaluation uses the
challenge's unchanged `./benchmark.sh ripemd160` with its ranked sandbox.

`dependencies.json` records reused public code and proofs. The inherited
Apache 2.0 license and notices apply. Earlier MODEXP work in the author's
repository, including an optimization found by Claude, informed this search.
