# EIP-8200 MODEXP: stack-v10a = 5788127e (stack-v9) plus the n=4 squaring group and the 256-bit tail

This image is our submission `5788127e` (stack-v9: `1954e3f4` plus the N1 and P1 cuts) plus seven more cuts of ours:
`n4a`, `n4f`, `offsets`, `depad`, `n4t`, `rare4` (the n=4 squaring kernel group) and `t256` (the 256-bit route tail).
`5788127e` is `1954e3f4` plus N1 and P1; `1954e3f4` is `a87239b0` plus B4, C2 and e3skip; `a87239b0` is `bdd36736`
(464,988 official) plus precopy256; and `bdd36736` is the promoted image `af797111` with two merged submissions
(`d0a1f9e9`, `984faab1`) and eight cuts of ours. Every one of those cuts is in this image.

5,537 bytes, 4,400 instructions (`5788127e`: 5,544 bytes, 4,359). Seed 0: 460,386 gas (`5788127e` 461,838).

## Merged from other submissions

| Source | Bytes | Change | Gas, every seed |
|---|---|---|---|
| `d0a1f9e9` (Th0rgal) | [4, 135), [864, 872) | EarlyWord guard; Fermat entry/return stack diet | -405 |
| `984faab1` (UsamaInayat) | [973, 994) | 256-bit window route setup block | -128 |

Our C2 cut (in `5788127e`) rewrote the whole dispatch prologue [0, 135) and our precopy256 cut replaced the window
route, so the exact bytes of both are superseded there; the Fermat check is carried into the new prologue and the
proof files are rebound. The seven new cuts do not touch either range. No cut of this image comes from another
submission.

## The seven new cuts

Each cut also edits `bytecode.hex`, `Bytes.lean`, `TnM128CandidateBytes` and the `TnM128CandidateArtifact`
instruction list; `ShiftJumpTargets` is regenerated from the final instruction list. `depad` and `t256` change the
length of the code, so most pcs after 2392 move and 90 proof files only renumber pcs, indices or memory offsets.

| Cut | Change | Gas |
|---|---|---|
| n4a | n=4 squarings read `a` from the `t` buffer at 0x840..0x8a0 (in the n=4 kernel `t` lives on the stack and is stored there at the end), so the squaring-to-squaring `MCOPY` is skipped; setup stages the base at `0x740 + 2 * 32n` (0x940 for n=8, 0x840 for n=4, a self copy) | n=4 group below |
| n4f | the n=4 squaring tail falls through into the counter block, its only predecessor: no `PUSH2 JUMP JUMPDEST` (12 gas per n=4 squaring) | n=4 group |
| offsets | computed-jump offset constants become label expressions: the M9 E6 pair, the small-path pair and the n=8 / n=4 multiply entry (3562 / 5309) | 0 |
| depad | every `PUSHn` with leading zero bytes shrinks to its minimal width; saves bytes for the others to use, 0 gas | 0 |
| n4t | the n=4 squaring tail tests `tn` from the stack before the counter and jumps straight to the next first row; the rare `tn != 0` case goes to its own block | n=4 group |
| rare4 | the n=4 tail tests `tn` (`DUP5`) before the stores; `tn != 0` goes to a block that subtracts `N` from the four `t` limbs in place on the stack (the `N` limbs are frame slots 7 to 10), zeroes `tn` and jumps back to the stores; the shared subtraction, select and `MCOPY` detour is gone for n=4 squarings | n=4 group |
| t256 | the 256-bit route's last windows (tail, whose only predecessor is 2391) move back inline at 2388, replacing `PUSH2 156b JUMP` and the tail `JUMPDEST` (12 gas per 256-bit vector); the five dead `JUMPDEST` pads at 2392 to 2396 go | -384 every seed |

The n=4 group (n4a, n4f, offsets, depad, n4t, rare4) saves 1,276.5 gas on average over 31 seeds on `5788127e`
(range -1,674 to -967); with t256 the total is -1,660.5 mean (-1,452 at seed 0). The two parts add exactly
(-1,276.5 and -384).

## Proof changes

- n=4 keeps its own memory model in `R4Loop`; the n=8 path is untouched. The round is `r4Step M = r4Mem M (red4 W)`
  (reduced limbs, overflow 0), `k` rounds, then one copy 2112 to 2368. The invariant carries the operand at 2112.
- `R4Math`, `R4Value`: `sub4`, `red4` and the borrow-chain lemma `sum d_i R^i = P + R^4 - N` that gives the
  `rare4` value (it equals `LazyCsub.value`).
- `R4Blocks`, `R4Runs`, `R4Bridge`, `R4Trace`: the new tail blocks (`st4`, `m4`, `rare4`), their runs and the
  operand window 2112 to 2208.
- `TnM128SetupZero` (new staging program, 10 instructions), `TnM128SetupEntry` (setup is 62 instructions),
  `Cios2Dispatch`, `SquareLoop` (new n=4 section), `StagedOperandMemory`, `LazyLoopMemory`, `LazySquareMemory`,
  `SquareLoopMem`: the staging path and the n=4 loop.
- `Exp.Subroutines.monpro` is removed: no consumer ever used it, and after n4a the generic n=4 multiply cannot be
  proved because it would read an unstaged operand (the generic MONPRO dispatch is unreachable). `ExpSubs` loses
  `subsMonpro`.
- Five dead files are deleted: `R4SquareScratchAgreement`, `CarryFullFast`, `CarryFullSpecializedFour`,
  `CarryFullSpecializedEight`, `CarryEntryLemmas` (no importer; they would not compile after n4a).
- t256: `tailProgram` without its `JUMPDEST` at 2388; `jumpProgram`, `run_jumpAt`, `Paths.jump` and
  `Paths.tailJump` are removed; slice `1891 48 2388` in `WindowPrecopyRoute`, `WindowTwentyOneGasCore` and
  `ArtifactWindowPaths`.
- Renumbering: `ShiftJumpTargets`, `ShiftPCs`, `FixedDirectPaths`, `WordEnds` and the shift, RootE3 and M9 files
  take the new pcs and indices. `Solution.lean` is unchanged.

## Artifact size

The generated `Artifact.lean` fails when S (distinct bytes per 64-byte chunk, summed), L (code length) and 8 per
chunk exceed 8,194. This image: S 1,922, L 5,537, 87 chunks, so S + L + 8 x 87 = 8,155 (39 below the limit).

## Gas

Python replica of the scorer, all 44 vectors, 0 wrong outputs of 1,364 runs for each sweep:

| Sweep | Image | Mean | sd |
|---|---|---|---|
| seed 0 + 30 seeds of `random.Random(8200)` | `5788127e` | 463,628.4 | 1,065.8 |
| | this image | 461,967.9 | 935.9 |
| 31 seeds of `random.Random(20261014)` | `5788127e` | 463,453.0 | 776.1 |
| | this image | 461,838.1 | 683.1 |

The paired saving is -1,660.5 mean on the first sweep (range -2,058 to -1,351) and -1,614.9 mean on the second
(same range).

A full build of `Challenge.Modexp.Submission.Solution` on these bytes exits 0 (2,326 jobs);
`Challenge.Modexp.Benchmark.candidate` depends on axioms `[propext, Classical.choice, Quot.sound]`. The Comparator
and the official scorer have not been run on these exact bytes.
