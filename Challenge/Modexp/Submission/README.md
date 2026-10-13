# EIP-8200 MODEXP: stack-v9 = 1954e3f4 (stack-v8) plus the N1 and P1 cuts

This image is our submission `1954e3f4` (stack-v8: `a87239b0` plus the B4, C2
and e3skip cuts) plus two more cuts of ours: N1 (negation loop without the
carry chain) and P1 (two CIOS frame transpositions). `a87239b0` is `bdd36736`
(464,988 official, the record) plus precopy256, and `bdd36736` is the promoted
image `af797111` with two merged submissions (`d0a1f9e9`, `984faab1`) and eight
cuts of ours.

5,544 bytes, 4,359 instructions (`1954e3f4`: 5,544 bytes, 4,361). Seed 0:
461,838 gas (`1954e3f4` 463,094, `a87239b0` 464,354, `bdd36736` 465,890,
`af797111` 467,695).

## Merged from other submissions

| Source | Bytes | Change | Gas, every seed |
|---|---|---|---|
| `d0a1f9e9` (Th0rgal) | [4, 135), [864, 872) | EarlyWord guard; Fermat entry/return stack diet | -405 |
| `984faab1` (UsamaInayat) | [973, 994) | 256-bit window route setup block | -128 |

Cut 11 (C2) below rewrites the whole of [0, 135) and the route head, so the
`d0a1f9e9` guard bytes are superseded by it; the Fermat check is carried into
the new prologue and its proof files are rebound.

## Our cuts

Each cut also edits `bytecode.hex`, `Bytes.lean`, `TnM128CandidateBytes` and
the `TnM128CandidateArtifact` instruction list; `ShiftJumpTargets` is
regenerated from the final instruction list. Cuts 1-9 are in `a87239b0`
(1-8 in `bdd36736`), cuts 10-12 are in `1954e3f4`, and cuts 13 and 14 are new
in this image. Cuts 10-12 keep every PC and every instruction index outside
their own ranges. Cuts 13 and 14 keep every pc outside their own ranges and
every existing `JUMPDEST` pc; instruction indices after 3977 move by -1 and
after 4011 by -2 (P1).

| # | Cut | Bytes | Change | Gas (31 seeds) | Main proof files |
|---|---|---|---|---|---|
| 1 | csub select tail | [4504, 4551) | `JUMPI` on the borrow flag instead of a branchless select | -117.3 mean | `Paths/CsubFixed`, `CsubCore` |
| 2 | route padding | [992, 2380) | two executed padding `JUMPDEST`s move behind the route's `RETURN` | -64 every seed | `WindowTwentyOne{Init,Loop,Core,GasCore}`, `ArtifactWindowPaths` |
| 3 | rsa-setup cut 1 | [4185, 4198) | n=4 first borrow limb uses the n=8 `DUP1 DUP3 SUB ... GT` pattern | -15.2 mean | `CsubFixed`, `ShiftPCs` |
| 4 | sqglue attempt 1 | [4198, 4258), [5058, 5062) | each squaring exit pushes its own CSUB return | -454 every seed | `TnM128SquareExit`, `R4Hooks`, `SquareLoop*`, `R4*` |
| 5 | rsa-setup cut 3 | [2883, 2896) | M9 quotient-estimate tail builds its all-ones mask early | -42 every seed | `ShiftPaths`, `ShiftTrace2`, `M9Mac*` |
| 6 | sqglue attempt 2 | [4198, 4258), 5058 | n=8 squaring exit resets the carry and advances the row pointer at entry; `TnM128Again` deleted | -154 every seed | `TnM128SquareExit`, `SquareLoop*`, `R4*` |
| 7 | layout-v1 | [3395, 3470), [3836, 3887), [5251, 5306) | the n0 frame slot holds limb n2 for n=8; +1 instruction | -420 every seed | 43 setup, reduction-row, cache and renumbering files |
| 8 | csub2 | [4335, 4518), byte 4195 | 16-instruction trial-subtraction limb step `y = N + b; d = T - y; b' = (T < y) \| (b > y)` | -144.5 mean | `CsubFixed`, `CsubCore` |
| 9 | precopy256 | [866, 2397), [5483, 5544) | precopied 256-bit window route | -1,536 every seed | `WindowPrecopy`, `WindowPrecopyRoute`, `WindowTwentyOne{Core,GasCore}`, `ArtifactWindowPaths`, index shift |
| 10 | B4 | [2499, 2512), [4209, 4258), [5060, 5061) | square counter lives in the dead `pdst` slot; the n=4 counter is fused into its entry | -403 every seed | `TnM128SquareExit`, `SquareLoop{,Blocks,Mem,Runs}`, `R4{Blocks,Loop,Runs,Trace}`, `Exp`, `ExpSubs` |
| 11 | C2 | [0, 132), [864, 878) | dispatch prologue and route head rewritten (below) | -673 every seed | `EarlyWord*`, `Fermat*`, `WindowTwentyOne{Entry,Positive,GasRoute,Correct}`, `ArtifactWindowPaths`, `MainDefs` |
| 12 | e3skip | [2455, 2472), [3357, 3383), [5461, 5465) | skip the e=3 re-dispatch after the M9 phase switch | -184 every seed | `RootE3*`, `FixedDirect*`, `ShiftTrace{2-5}`, `M9MacShift`, `ShiftPCs` |
| 13 | N1 | [2583, 2615) | negation loop without the borrow chain (below) | -296 every seed | `ShiftModel`, `ShiftStates`, `ShiftTrace{1,5}`, `ShiftCorrect`, `ShiftPaths`, `ShiftBlocks`, `RootE3{Memory,Trace}` |
| 14 | P1 | 84 bytes in [3403, 5428) | two frame transpositions in the CIOS frame (below) | -960 every seed | `TnCache*`, `CiosCachedRowFrames`, `TnM128{Setup*,Row*,Rows*,Reduction*,R4Reduction,R8*,Square*}`, `R4Trace`, `SquareLoop`, `SgtStep` |

| 15 | N2 (`blk2919`) | [2611, 2618) | remove 3 fall-through `JUMPDEST` pads at 2612..2614 by widening `PUSH0` at 2617 to `PUSH3 0` | -16 every seed | `ShiftPaths`, `ShiftTrace1`, `ShiftPCs` |
| 16 | E6b (`M9Mac.entryProgram`) | [2895, 2899) | fuse `JUMPDEST; PUSH0` at 2895..2896 into `PUSH1 0` | -21 every seed | `M9MacPrograms`, `M9MacBlocks`, `M9MacRun`, `ShiftJumpTargets` |
| 17 | `blk3125` + `blk3253` + `e3skip` pad | [3168, 3205), [3282, 3285), [3381, 3383) | narrow `PUSH5 2080` at 3168 to `PUSH2 2080` and absorb 4 instructions as dead `JUMPDEST`s at 3202..3204 and 3381..3382 so PCs from 3208 and indices from 2619 remain invariant | 0 every seed | `ShiftPaths`, `ShiftBlocks`, `ShiftStates`, `ShiftTrace{2,3}`, `RootE3Bindings`, `Paths/CsubFixed` |

Cuts 15, 16 and 17: 46 bytes differ from `5788127e` (`3f8e05cf`), all inside `[2611, 2618)`, `[2895, 2899)`, `[3168, 3205)`, `[3282, 3285)` and `[3381, 3383)`. Total gas saving is **-37 gas deterministically on every seed** (`462,538 -> 462,501` on the official draw, `461,838 -> 461,801` on Seed 0).

## Cut 10: B4, square counter

The chain init sets `pdst := count - 1` (count 16 or 1 on the stack) and no
longer writes `mem[0xa40]`. The per-square counter step reads `pdst` directly
(31 gas against 38), so `pdst` counts `count - 1` down to 0, and the n=4 entry
carries its own counter step (35 gas against a 15 gas trampoline plus 38).
The R4 exit literal changes from `PUSH2 1090` to `PUSH2 108a`. Saving at seed 0: RSA-1024
e=65537 -277, RSA-2048 e=65537 -112, the two e=3 vectors -7 each.

## Cut 11: C2, dispatch prologue

The old route path guarded on `(bs>32)|(es^32)|(ms^32)`, loaded the exponent
and modulus at `96+bs` and `128+bs`, and sent every miss through a 14 gas
trampoline. The new prologue tests `es` and `ms` first and sends a miss to the
generic path with an empty stack, with no trampoline. For `bs = 32` it loads
the exponent and modulus at fixed offsets (`CALLDATALOAD(0x80)`,
`CALLDATALOAD(0xa0)`); for `bs < 32` a short block computes `k = 32 - bs` and
rejoins the same code; `bs > 32` goes to the big-modulus entry (pc 238). The
Fermat check and the route head at 872 follow. Two `JUMPDEST` pads keep the
instruction count, and the width-hit jump at 861 now enters the new generic
block instead of the old adapter (so the adapter at pc 112 and its proofs are
gone). Case split in the proof: `es != 32` or `ms != 32` reaches 599 with the
stack the old miss produced; `bs = es = ms = 32` gives `[0, e, m]` at the
join; `bs > 32` reaches `BigCUMain.bigC_correct`, which accepts any stack.
`MainDefs.headerPCs0` becomes `[0, 2]` (a `PUSH1` at pc 0), and the route tail
bound in `WindowTwentyOneGasRoute` is 590 (precopy256's `steps_core` takes
`rest <= 600`).

## Cut 12: e3skip

After the M9 phase switch an e=3 input used to walk back through the
dispatcher. The phase switch now sets a marker `z = 30` (a new 14-instruction
block `SWAP16 PUSH2 06e0 MSTORE PUSH1 1e SWAP16 ...`) and the cleanup jumps
straight to 2471; the stub block at 3378 is no longer visited (its proof is
deleted) and the dispatcher's width test is one merged 13-instruction test. Saving: -81 gas per e=3 vector and
-11 per e=65537 vector (-184 on every seed). In the proofs, `rideSlots` takes
`z` as its last riding slot, `run_cleanup` goes `cleanupState (ofNat d)` to
`frameState target` for `d` in `{0, 30}`, and `RootE3Correct` casts the e=3
trace end `frameState 2471` to `FixedDirectStates.e3go` by `rfl`.

## Cut 13: N1, negation loop

A setup loop stores `NEG = 2^(256n) - m` limb by limb. The old loop ran a full
borrow chain (68 gas per limb). The low limb of the modulus is odd on this
route, so `NOT m0 + 1` never carries and every later limb is plain `NOT mi`.
The new loop keeps a flag on top of the stack: `JUMPDEST DUP2 MLOAD NOT ADD
DUP2 PUSH2 0500 ADD MSTORE PUSH0 DUP2 PUSH1 1f NOT ADD SWAP2 PUSH2 0a1d JUMPI`
(55 gas per limb), followed by four `JUMPDEST` pads before pc 2615. Limb `j`
stores `NOT m_j + flag`; the flag is 1 for limb 0 only, and the `PUSH0` clears
it. The block at 2583 pushes `PUSH2 0ac0 MLOAD PUSH1 01` (pointer first, flag
on top). The range [2574, 2615) keeps its length and its 29 instructions, so N1
alone leaves every pc and every instruction index outside it unchanged. Saving: -48 on each of
the two RSA-1024 vectors and -100 on each of the two RSA-2048 vectors (-296 on
every seed). In the proofs, `negStep` stores `NOT m_j + flag` and clears the
flag, `negStep_invariant` and `neg_represents` take the odd modulus (every
caller already had it), and the loop and exit states carry the flag on top.

## Cut 14: P1, CIOS frame transpositions

In the n=8 reduction frame the cells for limbs n5 and n6 sit in slots 15 and
16, which need the far cell form (`DUPs DUP10 DUP4 DUP3 MUL SWAP2 DUP5 MULMOD`,
8 instructions, 31 gas). A limb in slot 14 or less uses the near form (`DUP2
DUP(s+1) MUL DUP10 DUP(s+2) DUP5 MULMOD`, 7 instructions, 28 gas). P1 swaps
`ninv` (slot 11) with n5 (slot 15) and `tn` (slot 8) with n6 (slot 16). `ninv`
and `tn` are read once per row at shallow depth, so every DUP and SWAP index
they use stays at or below 16, and only the n5 and n6 cells change gas: -3
each. 160 rows per seed run these cells (152 n=8 rows and 8 n=4 multiply
rows), so 160 x 2 x -3 = -960 on every seed (-24 on each RSA-1024 vector, -96
on RSA-2048 e=3, -816 on RSA-2048 e=65537). The edits are 84 bytes in the setup
loads, the multiply setup, the row head, the two cells (each padded to keep
later pcs), the tail, the exit, the reset between squarings, the n=4 squaring
entry, the first row and the n=4 multiply head. Instruction indices after 3977
move by -1 and after 4011 by -2; no existing `JUMPDEST` pc moves.
Six proof files needed hand merges against B4 and the new indices:
`SgtStep`, `TnM128SgtStep`, `R4Trace`, `TnM128CandidateBlocks`,
`TnM128SquareFinishSteps` and `SquareLoop`.

## Cuts 15, 16, and 17: N2 (`blk2919`), E6b (`M9Mac.entryProgram`), and Index/PC Restoration

- **Cut 15 (N2, `blk2919`, `[2611, 2618)`)**: Replaces `JUMPDEST; JUMPDEST; JUMPDEST; JUMPDEST; POP; POP; PUSH0` (`5b 5b 5b 5b 50 50 5f`, 7 bytes, 7 instructions, 12 gas) on the negation loop fall-through with `JUMPDEST; POP; POP; PUSH3 0x000000` (`5b 50 50 62 00 00 00`, 7 bytes, 4 instructions, 10 gas). Exact same 7-byte footprint, saving `-2` gas per M9 setup call × 8 calls = **-16 gas on every seed**.
- **Cut 16 (E6b, `M9Mac.entryProgram`, `[2895, 2899)`)**: Replaces `JUMPDEST; PUSH0; DUP5; JUMP` (`5b 5f 84 56`, 4 bytes, 4 instructions, 14 gas) at the fall-through entry from `blk3026` with `PUSH1 0x00; DUP5; JUMP` (`60 00 84 56`, 4 bytes, 3 instructions, 13 gas). Exact same 4-byte footprint, saving `-1` gas per M9 iteration × 21 iterations = **-21 gas on every seed**.
- **Cut 17 (`blk3125` + `blk3253` + `e3skip` dead pad, `[3168, 3205)`, `[3282, 3285)`, `[3381, 3383)`)**: Narrows `PUSH5 2080` (`64 00 00 00 08 20`, 6 bytes) at PC 3168 (`blk3125`) to `PUSH2 2080` (`61 08 20`, 3 bytes), updates the literal jump target of `blk3204` at PC 3282 from `3198` to `3195`, appends three dead `JUMPDEST`s at PC 3202..3204 after `blk3253`'s `JUMP`, and replaces the dead 2-byte `PUSH1 2` (`60 02`) at PC 3381..3382 after `e3skip`'s `JUMP` with two dead `JUMPDEST`s (`5b 5b`). This restores the total instruction count to `4,359` and keeps every PC from `3208` onwards and every instruction index from `2619` onwards 100% invariant.

## Artifact size

The generated `Artifact.lean` fails when S (distinct bytes per 64-byte chunk,
summed), L (code length) and 8 per chunk exceed 8,194. This image: S 1,936,
L 5,544, 87 chunks, so S + L + 8 x 87 = 8,176 (18 below the limit).

## Gas

Python replica of the scorer, seed 0 plus 30 seeds, all 44 vectors, 0 wrong
outputs of 1,364 runs:

| Image | Seed 0 | Mean | sd |
|---|---|---|---|
| `af797111` | 467,695 | 469,624.4 | 1,155.8 |
| `bdd36736` (cuts 1-8) | 465,890 | 467,680.4 | 1,065.8 |
| `a87239b0` (cut 9) | 464,354 | 466,144.4 | 1,065.8 |
| `1954e3f4` (cuts 10-12) | 463,094 | 464,884.4 | 1,065.8 |
| `5788127e` (cuts 13-14) | 461,838 | 463,628.4 | 1,065.8 |
| this image (cuts 15-17) | 461,801 | 463,591.4 | 1,065.8 |

A full build of `Challenge.Modexp.Submission.Solution` on these bytes exits 0;
`Challenge.Modexp.Benchmark.candidate` depends on axioms
`[propext, Classical.choice, Quot.sound]`.
