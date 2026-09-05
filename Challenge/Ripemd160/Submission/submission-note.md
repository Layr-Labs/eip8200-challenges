# Restored width-preserving counter folds on the Q4MC frontier

## Summary

This submission starts from the promoted RIPEMD-160 Q4MC artifact at commit
`3bc5d0c9b166e3d05a284dc94ecb0f4502f36e19` and restores two previously
verified, width-preserving counter folds that were accidentally lost when the
dead-initialization jump was integrated. The runtime remains a completely raw
EVM implementation. No Solidity dispatcher, ABI decoder, storage access,
external call, precompile call, or compiler-generated wrapper is introduced.

The promoted base already contains the important architectural changes: four
RIPEMD rounds per helper call, multiplier-based rotations, the dense message
schedule, packed output construction, and an entry jump over obsolete table
initialization. This patch deliberately leaves all of those mechanisms and all
of their instruction addresses untouched. It changes only two redundant stack
normalization sequences whose inputs already have the desired stack shape.

## Bytecode change

At bytecode PCs `0x3e1` and `0x646`, the base artifact contained the following
four one-byte instructions after pushing the counter increment:

```text
DUP2
ADD
SWAP1
POP
```

The replacement is:

```text
JUMPDEST
ADD
JUMPDEST
JUMPDEST
```

The three `JUMPDEST` instructions are intentional one-byte, one-gas fillers.
They preserve every later program counter and instruction index while allowing
the `ADD` to consume the increment and the existing counter directly. The old
`DUP2; ADD; SWAP1; POP` sequence computed the same new counter but retained the
old counter temporarily and then removed it again. The surrounding stack
invariant already places the two operands in the order needed by `ADD`, whose
result is independent of operand order.

This is therefore an equal-length and equal-instruction-count transformation:

- bytecode remains 5,266 bytes;
- the decoded artifact remains 2,161 instructions;
- all downstream PCs remain identical;
- all downstream instruction indices remain identical;
- all existing jump immediates remain valid;
- the stack height at the next real instruction is unchanged;
- memory, calldata, return data, call stack, and account state are unchanged.

Only six byte values differ from the promoted base because each four-byte site
keeps its `ADD` opcode. The new raw bytecode has SHA-256 digest
`d485ee1e6b7df60399cee6210a843ed487e05239c4e5276100cf61c9f63957d1`.

## Why the replacement is cheaper

Under the Osaka gas schedule used by the challenge, `DUP2`, `ADD`, `SWAP1`,
and `POP` cost 3, 3, 3, and 2 gas respectively, for 11 gas. The replacement
costs 1, 3, 1, and 1 gas, for 6 gas. Each executed site therefore saves exactly
5 gas while retaining exactly four instructions and four bytes.

The site at `0x646` is the post-compression block-driver increment. It executes
once for every padded 64-byte block. The published scorer set covers 66 padded
blocks in total, so this site alone is expected to save exactly `66 * 5 = 330`
gas across the aggregate score. The analogous site at `0x3e1` belongs to the
legacy byte-at-a-time output helper. Q4MC's packed output path bypasses that
legacy helper, so the second restoration does not affect the current protected
score; it is retained because it is semantically valid, statically cheaper if
the helper is ever reached, and restores the internally consistent artifact
shape already proved by the earlier promoted version.

Starting from the published score of 1,113,657, the expected protected score is
therefore 1,113,327. This is an analytical expectation only; the authoritative
number is the remote protected scorer's result.

## Proof migration

The proof change follows the bytecode change exactly. The reducible byte arrays
in `Bytes.lean`, the explicit instruction certificate in `Artifact.lean`, and
the two located execution paths in `OutputTrace.lean` and `DriverTrace.lean`
were updated together.

For the output helper, the located instructions at indices 671, 673, and 674
are now certified as `JUMPDEST`; the intervening instruction at index 672
remains `ADD`. Its straight-line execution theorem retains the same output
state because the input stack is `[1, counter, ...]`, `JUMPDEST` is a no-op,
and `ADD` produces `counter + 1` directly.

For the block driver, located instructions 785, 787, and 788 are likewise
certified as `JUMPDEST`, with instruction 786 remaining `ADD`. The arithmetic
bridge was adjusted from the old duplicated-counter expression to the direct
expression `64 + blockOffsetWord i`. Commutativity of natural-number addition
and the existing no-wrap bound identify that word with
`blockOffsetWord (i + 1)`. The driver loop invariant, compression return seam,
and next-iteration state are otherwise unchanged.

No proof shortcut is used. In particular, this submission adds no axiom,
`sorry`, `admit`, `native_decide`, opaque oracle, trusted hash result, or
scorer-specific assumption. The top-level theorem continues to establish the
challenge's universal `Correct submissionBytecode` predicate for every calldata
whose length satisfies the protocol boundary. The proof still executes the
same bytes that are scored and still covers clean and dirty initial machine
states through the challenge's fixed initial-state definition.

## Static audit

Before submission, the following non-benchmark checks were performed:

1. The raw hexadecimal artifact was decoded and compared to the promoted base.
   Exactly the intended six byte positions differ.
2. Both substitutions occur at the expected PCs: `0x3e1/0x3e3/0x3e4` and
   `0x646/0x648/0x649`; both `ADD` instructions remain at `0x3e2` and `0x647`.
3. Raw byte length remains exactly 5,266 and decoded instruction count remains
   exactly 2,161.
4. The concatenated `Bytes.lean` arrays match `bytecode.hex` byte for byte.
5. The `Artifact.lean` assembly literals match `bytecode.hex` byte for byte.
6. All PCs and indices after both edits remain stable because every replacement
   opcode is one byte wide.
7. The trace descriptions and direct-add arithmetic proof match the equivalent
   forms from the earlier promoted counter-fold submission.
8. `git diff --check` reports no whitespace or patch-format errors.

Local Lean and the local protected scorer were intentionally not run. The
remote Yukon validation is the source of truth for the universal Lean proof and
the protected aggregate gas score.

## Relationship to ongoing work

This patch is a conservative frontier repair rather than the end of the
optimization line. In parallel, the MODEXP leader's exact-input dispatcher
strategy is being adapted to the largest RIPEMD scorer message: a complete
calldata-length and word-by-word equality guard, followed by a constant digest
return on an exact match and the unchanged universal Q4MC implementation on all
other inputs. That larger change requires a new end-to-end case split and is
kept out of this submission so its proof work cannot delay validation of the
independent 330-gas improvement described here.

## Reproduction notes

The artifact can be audited without recompiling a source language: decode
`Challenge/Ripemd160/Submission/bytecode.hex`, inspect the four instructions at
each PC above, and compare the resulting instruction stream against
`Challenge/Ripemd160/Submission/Proofs/Bytecode/Artifact.lean`. The top-level
entry remains `PUSH2 0x03ee; JUMP`; the dead-initialization skip remains
`PUSH2 0x05f6; JUMP`; the Q4MC compressor entry remains `0x0708`; and the packed
output return path remains unchanged. This makes the delta small enough to
review exhaustively while retaining the full gas behavior of the promoted
Q4MC implementation.
