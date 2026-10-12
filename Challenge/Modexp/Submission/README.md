# EIP-8200 MODEXP: d0a1f9e9 + 984faab1 merge plus subtraction-tail, 256-bit route, n=4 CSUB and squaring-glue cuts

This submission combines two earlier submissions. Both build on the promoted
image `af797111` and edit disjoint byte ranges of the 5,483-byte bytecode.

| Source | Bytes | Change | Gas at seed 0 |
|---|---|---|---|
| `d0a1f9e9` (Th0rgal) | [4, 135), [864, 872) | EarlyWord guard and Fermat entry/return stack diet | -405 |
| `984faab1` (UsamaInayat) | [968, 994) | 256-bit window route setup block, PC- and instruction-count-neutral | -128 |
| this submission | [4511, 4551) | Conditional-subtraction select tail: `JUMPI` on the borrow flag instead of a branchless select; PC- and instruction-count-neutral | -60 at seed 0, -117 mean |
| total | all three | all three | -593 at seed 0 (467,102), -650 mean over 31 seeds |

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

Seed 0: 467,102 (base 467,695). The merged edits are deterministic (-533 on every seed);
the subtraction tail saves 60 gas per subtraction that fires, so its saving varies by seed
(-36 to -192, mean -117 over 31 seeds).

## Subtraction tail proofs

`Proofs/Fast/Paths/CsubFixed.lean` splits the tail into `csFixedTailSub` and `csFixedTailKeep`;
`Proofs/Fast/CsubCore.lean` proves both tails and splits `gasSteps_csFixedTail{8,4}` on the borrow flag.
`subReturnedState` and every downstream statement are unchanged.

## Further cuts in this version (all original, PC- and instruction-count-neutral outside their ranges)

| Change | Bytes | Gas (31 seeds) |
|---|---|---|
| n=4 CSUB first limb `DUP1 DUP3 SUB ... GT` (dead `PUSH0` pad after the `JUMP`) | [4185, 4198) | -15 mean |
| 256-bit route: two padding `JUMPDEST`s moved past the route's `RETURN` | [992, 2380) shifted by 2 | -64 every seed |
| Squaring loop: width-specific CSUB return, the per-squaring width dispatch at 4232 removed | [4198, 4258), [5058, 5062) | -454 every seed |

Total vs `af797111`: seed 0 466,575 (-1,120), mean over 31 seeds 468,440.9 (-1,183.5).
