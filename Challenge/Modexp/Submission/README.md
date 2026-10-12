# EIP-8200 MODEXP: stack-v6 = bdd36736 plus a precopied 256-bit window route

This image is our accepted submission `bdd36736` (464,988 official) plus one
more cut of ours, precopy256. `bdd36736` itself is the promoted image
`af797111` with two merged submissions (`d0a1f9e9`, `984faab1`) and eight
cuts of ours.

5,544 bytes, 4,361 instructions. Seed 0: 464,354 gas (`af797111` 467,695,
`bdd36736` 465,890).

## Merged from other submissions

| Source | Bytes | Change | Gas, every seed |
|---|---|---|---|
| `d0a1f9e9` (Th0rgal) | [4, 135), [864, 872) | EarlyWord guard; Fermat entry/return stack diet | -405 |
| `984faab1` (UsamaInayat) | [973, 994) | 256-bit window route setup block | -128 |

The ranges are disjoint, so `bytecode.hex` takes each byte from whichever
submission changed it. Files changed by one submission are taken from it
unchanged (`EarlyWord*`, `Fermat*`, `WindowTwentyOne{Entry,GasRoute,Positive}`
from `d0a1f9e9`; `WindowTwentyOne{Init,Loop,GasCore}` from `984faab1`).
`Bytes.lean`, `TnM128CandidateBytes`, `TnM128CandidateArtifact` and
`ArtifactWindowPaths` were three-way merged against `af797111` (disjoint hunks).

## Our cuts

Each cut also edits `bytecode.hex`, `Bytes.lean`, `TnM128CandidateBytes` and
the `TnM128CandidateArtifact` instruction list; `ShiftJumpTargets` is
regenerated from the final instruction list. Cuts 1-8 are in `bdd36736`.

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
| 9 | precopy256 | [866, 2397), [5483, 5544) | precopied 256-bit window route (below) | -1,536 every seed | `WindowPrecopy`, `WindowPrecopyRoute`, `WindowTwentyOne{Core,GasCore}`, `ArtifactWindowPaths`, index shift |

## Cut 9: precopied 256-bit window route

The old route kept a few modulus copies on the stack and refilled them
between windows. The new setup stores `e >> 3` at `mem[0x200]` and pushes all
315 modulus copies (`DUP2`, then 314 `DUP1`) before the accumulator. Each
4-bit window is then four squarings plus
`PUSH2 X MLOAD PUSH2 01e0 AND MLOAD MULMOD`, which consumes five copies with
no refill. The exponent sits under the pool, so the first digit is read from
memory; the setup stays gas-neutral.

The new route does not fit in the old region:

- 866..2387: table, setup, pool, first lookup and 60 windows.
- 2388..2391: `PUSH2 156b JUMP`.
- 2392..2396: five unreachable `JUMPDEST`s, so pc 2397 (a live target) stays fixed.
- 5483..5543 (appended, 61 bytes): `JUMPDEST`, the last two windows, the final digit and `RETURN`.

Every PC outside the route is unchanged. Instruction indices from pc 2397
shift by -80 (index 1978 becomes 1898). The saving is 48 gas per 256-bit
route vector (60 saved, 12 spent on the jump), and 32 vectors take the route,
so -1,536 on every seed.

Proofs:

- `Proofs/Bytecode/WindowPrecopy.lean` (new): one window over any pool, the
  window chain, and the `DUP1` pool push.
- `Proofs/Bytecode/WindowPrecopyRoute.lean` (new): the route from setup to
  `RETURN`, including the jump to 5483.
- `WindowTwentyOneCore`, `WindowTwentyOneGasCore` and `ArtifactWindowPaths`
  are rebound to the new route slices.
- Index facts at instruction index 1978 or above are shifted by -80 in the
  RSA proof files (`ShiftPCs`, `ShiftPaths`, `ShiftTrace1-4`, `CsubFixed`,
  `R4Blocks`, `M9Mac{Blocks,Chain}`, `TnM128*` and others). PCs and theorem
  names are unchanged.
- `ShiftJumpTargets` lists are regenerated (new literal target 5483).
- `Solution.lean` is unchanged.

## Artifact size

The generated `Artifact.lean` hits `maxRecDepth` when S (distinct bytes per
64-byte chunk, summed) plus L (code length) is too large; probes passed at
7,498 and failed at 7,507. This image: S 1,922, L 5,544, S + L 7,466.

## Gas

Python replica of the scorer, seed 0 plus 30 seeds, all 44 vectors:

| Image | Seed 0 | Mean | sd |
|---|---|---|---|
| `af797111` | 467,695 | 469,624.4 | 1,155.8 |
| `bdd36736` (cuts 1-8) | 465,890 | 467,680.4 | 1,065.8 |
| this image (cut 9) | 464,354 | 466,144.4 | 1,065.8 |

A full build of `Challenge.Modexp.Submission.Solution` on these bytes exits 0;
`Challenge.Modexp.Benchmark.candidate` depends on axioms
`[propext, Classical.choice, Quot.sound]`.
