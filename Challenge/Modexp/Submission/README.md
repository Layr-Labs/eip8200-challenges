# EIP-8200 MODEXP: merge of two disjoint byte edits (d0a1f9e9 + 984faab1)

This submission combines two earlier submissions. Both build on the promoted
image `af797111` and edit disjoint byte ranges of the 5,483-byte bytecode.

| Source | Bytes | Change | Gas at seed 0 |
|---|---|---|---|
| `d0a1f9e9` (Th0rgal) | [4, 135), [864, 872) | EarlyWord guard and Fermat entry/return stack diet | -405 |
| `984faab1` (UsamaInayat) | [968, 994) | 256-bit window route setup block, PC- and instruction-count-neutral | -128 |
| merged | both | both | -533 (467,162) |

Both edits keep every PC and every instruction index outside their own
ranges. The merged `bytecode.hex` takes each byte from whichever submission
changed it. No byte was changed by both.

## Proof tree

- Files changed by one submission only are taken from that submission
  unchanged: `EarlyWord*`, `Fermat*`, `ShiftJumpTargets`,
  `WindowTwentyOneEntry`, `WindowTwentyOneGasRoute`, `WindowTwentyOnePositive`
  (d0a1f9e9) and `WindowTwentyOneInit`, `WindowTwentyOneLoop`,
  `WindowTwentyOneGasCore` (984faab1).
- Files changed by both are three-way merged against `af797111`; every hunk
  is disjoint: `Bytes.lean` (chunks 0-2 and 13 from d0a1f9e9, chunk 15 from
  984faab1), `Proofs/Fast/TnM128CandidateBytes.lean` (same chunks),
  `Proofs/Fast/TnM128CandidateArtifact.lean` (instruction indices 0-77, 618
  and 624 from d0a1f9e9, 718-738 from 984faab1) and
  `Proofs/Bytecode/ArtifactWindowPaths.lean` (adapter and Fermat slices from
  d0a1f9e9, init/trampoline/entry slices from 984faab1).
- `WindowTwentyOneGasCore.steps_core` keeps its statement, so d0a1f9e9's
  shorter core stack (`[exponentWord, baseSize]`) feeds 984faab1's loop proofs
  unchanged.

## Gas

Seed 0: 467,162 (base 467,695). The change is deterministic: every seed is
533 gas below the base image.
