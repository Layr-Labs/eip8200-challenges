# EIP-8200 MODEXP: stack-v8 = a87239b0 (precopy256) plus the B4, C2 and e3skip cuts

This image is our submission `a87239b0` (stack-v6: `bdd36736` plus precopy256)
plus three more cuts of ours: B4 (square counter), C2 (dispatch prologue) and
e3skip (e=3 re-dispatch skip). `bdd36736` (464,988 official, the record) is the
promoted image `af797111` with two merged submissions (`d0a1f9e9`,
`984faab1`) and eight cuts of ours; `a87239b0` added cut 9.

5,544 bytes, 4,361 instructions (both unchanged from `a87239b0`). Seed 0:
463,094 gas (`a87239b0` 464,354, `bdd36736` 465,890, `af797111` 467,695).

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
(1-8 in `bdd36736`); cuts 10-12 are new in this image and keep every PC and
every instruction index outside their own ranges.

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

Cuts 10-12: 235 bytes differ from `a87239b0`, all inside the ranges above.

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

## Artifact size

The generated `Artifact.lean` fails when S (distinct bytes per 64-byte chunk,
summed), L (code length) and 8 per chunk exceed 8,194. This image: S 1,933,
L 5,544, 87 chunks, so S + L + 8 x 87 = 8,173 (21 below the limit).

## Gas

Python replica of the scorer, seed 0 plus 30 seeds, all 44 vectors, 0 wrong
outputs of 1,364 runs:

| Image | Seed 0 | Mean | sd |
|---|---|---|---|
| `af797111` | 467,695 | 469,624.4 | 1,155.8 |
| `bdd36736` (cuts 1-8) | 465,890 | 467,680.4 | 1,065.8 |
| `a87239b0` (cut 9) | 464,354 | 466,144.4 | 1,065.8 |
| this image (cuts 10-12) | 463,094 | 464,884.4 | 1,065.8 |

The three new cuts are deterministic: -1,260 on every seed against
`a87239b0` (-403, -673, -184). Over 2,000 further seeds this image has mean
464,721.5 and sd 999.1.

A full build of `Challenge.Modexp.Submission.Solution` on these bytes exits 0;
`Challenge.Modexp.Benchmark.candidate` depends on axioms
`[propext, Classical.choice, Quot.sound]`. The Comparator and the official
scorer have not been run on these exact bytes.
