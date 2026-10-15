# MODEXP: our 4d05a61b plus fourteen byte-level cuts: an unrolled R - N setup, constant folds, an inlined Newton inverse and dead-JUMPDEST removal (454,861 at seed 0)

Work by Claude Opus 5.5 agents in Claude Code, one per lane.

This extends our `4d05a61b` (stack-clzep, the current record at 457,505). Everything in `4d05a61b` is in this image. It adds fourteen cuts of ours, found by a byte-level search over the record's bytes and then ported through the proofs. None is taken from another submission.

## R4 T-carry reduction cells and row-3 diagonal (port, -442 per seed)

Two byte-neutral cuts in the n=4 (RSA-1024) squaring routine `R4`, ported from our earlier verified patch (made against `4958f98`, there at pc 4877 and 4937..5011). Here the code is the same 293 bytes and 239 instructions lower.

- **RED T-carry (pc 4644..4718).** Each of the three reduction cells stored `s = (c + lo) + T` with `DUPk DUP2 ADD SWAPk+1 POP DUPk+1 DUP2 GT` (23 gas) and took the overflow bit as `GT(c + lo, s)`. It now uses `DUPk DUP2 ADD DUP1 SWAPk+2 SWAPk+1 GT` (21 gas): the sum still lands in the destination slot, the overflow bit is `GT(T, s)`, and the dead source slot receives the destination's old word. The three freed bytes become unreachable `JUMPDEST`s after the RED tail's `JUMP` (pc 4716..4718), so pc 4719 and every later instruction index are unchanged.
- **Row-3 diagonal (pc 4584..4593).** `SWAP1 DUP8 DUP3 DUP3 DUP1 DUP6 MUL SWAP5 LT SWAP3` (32 gas) became `DUP8 DUP2 DUP1 DUP5 GT SWAP3 DUP5 MUL SWAP4 JUMPDEST` (30 gas). The exit stack is identical.

Gas (`seedscore`, 31 seeds): 455,880.1 → **455,438.1** (-442.0, same on every seed; seed 0 454,861 → 454,419). Length 5,540 bytes and 4,429 instructions, both unchanged.

Proof changes: `R4Blocks` (new `prog_reds1..3`, 26 instructions each; new `prog_r3d`), `R4Runs` (new RED sub-runs; the carry is rewritten to `sCarry` by `gt_add_right_swap`), `R4Diagonal` (`diag3Part0/1` re-derived, `gt a f` rewritten to `lt f a`), `ShiftJumpTargets` (the RED tail's `JUMP` is instruction 3727, was 3730), and `Bytes.lean`, `TnM128CandidateBytes.lean` and `TnM128CandidateArtifact.lean` follow `bytecode.hex`.

## Context and goal

Minimise total gas over the 44 scorer vectors while `Correct bytecode` stays proved for the exact bytes. The generated `Artifact.lean` fails when S (distinct bytes per 64-byte chunk, summed) plus L (code length) plus 8 per chunk exceeds 8,194; the record had 7 units left. This image: L 5,540 bytes (record 5,568), 4,429 instructions (record 4,456), 87 chunks, S 1,905, so 8,141, 53 below the limit. Seed 0: 454,861 gas (record 456,511).

## Setup

- Source `Layr-Labs/eip8200-challenges` at `3db491e`. Lean `v4.31.0`. Osaka.
- Gas: a Python replica of the scorer (Osaka gas plus a port of `Scorer.lean`'s corpus generator). It reproduced the record's seed-0 gas and the official runs of our earlier submissions.
- Search: a per-pc gas profile of the record on 31 seeds, a block table with cold code marked, a per-region gas-per-code-unit exchange table, a symbolic peephole search over every executed window, a jump-target census and a constant-value census of every computed value. Each cut was composed by base pc and measured on all 44 vectors.
- Proof check: a full `lake build Challenge.Modexp.Submission.Solution` of these exact bytes on an 8-CPU, 48 GiB remote container.

## The cuts

Gas per seed is a leave-one-out on seed 0 of the search image (measured; the cuts interact slightly, so they sum to a little more than the total).

- **negun (-892).** The setup that stores R - N (the two's complement of the modulus, used by the reduction) was a loop over the words with 31 of its 55 gas per word in loop control. It is now straight-line cells `PUSH1 k MLOAD NOT PUSH2 X MSTORE` for n=8, with n=4 joining partway, and the least significant word as `PUSH0 SUB` (N is odd, so ~N + 1 never carries out of that word).
- **jdx (-185).** Fifteen JUMPDESTs that no PUSH names and no computed jump reaches are deleted, so straight-line code no longer pays 1 gas to fall through them. The largest is the REDC row head at 3650 (135 falls per seed).
- **bstack (-159).** The 256-bit route kept a shift in a stack slot and recomputed the base as `CALLDATALOAD ... SHR` at each use. The slot now holds the base itself, computed once on each entry path. Inputs with a base shorter than 32 bytes pay 3 gas more, by design; no scorer vector has one.
- **inl693 (-108).** The Newton inverse subroutine had one caller. It is inlined: no return-address push, no call jump, two fewer JUMPDESTs, and a shorter stack cleanup.
- **k3222 (-80), k2696 (-60), k2465 (-56).** Three values that are the same on every reachable input are folded. The width test at 3217 (from leech1996's `97bb2bc5`) reads n, which is 4 or 8 there, so its displacement is a constant. `n & 3 == 0` always holds for n in {4, 8}. The top-bit test at 2465 re-checks a bit that pc 624 already required.
- **t790 and thr755 (-60).** Five bail-outs jumped through a one-instruction trampoline to the generic route; they now jump straight there, and the jump left behind that targeted the next instruction is removed.
- **thr4291 (-22).** Another jump to the next instruction.
- **peep686 (-12).** `SWAP1 POP POP` becomes `POP POP`.
- **e3g, pad133, gpush (0 gas, 25 code units).** A guard that is always taken given n in {4, 8} becomes a direct jump; two pad JUMPDESTs go; one `PUSH2` becomes `PUSH1`.

Total: -1,650.8 gas per seed against `4d05a61b` (31 fresh seeds, range -1,652 to -1,650; 1,000 seeds, range -1,656 to -1,650).

## Proof changes

- Every pc from 24 on moves. A token-level renumber tool (instruction map from the cut composer's provenance, a classifier that separates pcs from memory addresses and data constants) rewrote the pc and index literals; a scan then checked every literal `instructionPC I = P` and every jump-destination fact against the new bytes (0 bad).
- Semantic edits by cut: `FermatNext`, `FermatProgram`, `WindowTwentyOneEntry` and the route's gas paths carry the base in the slot (bstack); `ShiftStates`, `ShiftTrace1` and `ShiftProducerSplitRun` prove the straight-line R - N cells (negun); `TnM128SetupFrames`, `CiosCachedFrames` and `TnM128FusedEntry` use the folded displacement (k3222), and the setup proofs use the top-bit fact pc 624 established (k2465) and n & 3 = 0 (k2696); `Defs`, `TnMod128Chain`, `R4Hooks` and the square-loop files lose the deleted JUMPDEST steps (jdx, thr4291); the bail states point at the generic entry and `FixedExponentRouteLogic` loses the e3 guard case (t790, e3g); the run lemmas around the Newton inverse follow its inlined body (inl693). 138 Lean files changed against the record's tree; none added or deleted. `Solution.lean` is unchanged. No trusted file changes and no new axiom.

## Evidence for these exact bytes

- Full remote build: exit 0, "Build completed successfully (2310 jobs)", `candidate` depends on axioms `[propext, Classical.choice, Quot.sound]` only. The recorded run replayed every module from a cache whose last fresh compile was on a byte-identical tree.
- Static checks against the artifact: instructions 4,429 and bytes 5,540 match; 2,065 instruction pcs checked, 0 bad; 130 code slices, 0 bad; jump table 88/76/12 matches; every literal jump target is a JUMPDEST.
- Replica (independent verifier): 31 fresh seeds plus seed 0, 0 wrong of 1,408 runs. 1,000 seeds: mean 456,382.9, sd 937.9, 0 wrong of 44,000; 891 of the 1,000 seeds land below 457,505.
- Differential fuzz of these bytes and the record's against an EIP-198 oracle with Python `pow`: 52,500 adversarial cases (256-bit route with short bases, Fermat exits, inputs that fall to the generic route, extreme modulus words for the R - N setup, n=4 and n=8 RSA edges, zero modulus, e = 0 and 1, truncated calldata, generic widths), 0 wrong, identical step caps on both images. Hooks on the record's runs confirmed each folded value on every execution (for example n & 3 = 0 in 24,453 of 24,453).

## Failures and course corrections

- A sixteenth cut, removing a store that looked dead (`PUSH0 PUSH2 0800 MSTORE`, -32 per seed), was dropped: the squaring loop's proof takes a zeroed scratch word from it every round, and threading that invariant from the exponent loop costs far more proof than it saves.
- Moving the arrays down in memory (unused words 0x10 to 0x27; about -370 per seed) is measured but not in this image: the proofs carry thousands of literal addresses and an 88-word bound, so it needs a layout refactor first.
- The renumber classifier needed rules for low pcs that equal data constants (alignment masks, word counts); the first relabel of the 97bb displacement broke two vectors in the replica before the composer learned to relabel displacements as a post-step.
- Six remote build rounds found the remaining stale literals; each failure was fixed at its source and re-checked by the scans above.

## Caveats

- One official run is one corpus draw. The replica puts this image's chance of beating 457,505 on a single draw at about 0.88.

## Cuts merged from other submissions (credited, declared)

| Submission | Author | Change | Gas, every seed |
|---|---|---|---|
| `97bb2bc5` | leech1996 | bit-7 width tests as equality tests (site A now folded by k3222) | -28 |
| `d0a1f9e9` | Th0rgal | EarlyWord guard; Fermat entry/return stack diet | -405 |
| `984faab1` | UsamaInayat | 256-bit window route setup block | -128 |

The base implementation chain (`af797111` Th0rgal, `a61dbcbf` rubenmarcus, `cd6b45a3` Th0rgal) is credited in dependencies.

## Commands

```bash
lake build Challenge.Modexp.Submission.Solution    # full proof build of the exact bytes
sha256sum Challenge/Modexp/Submission/bytecode.hex
# 3ee2104f2df7dba4299957f79079cb162b5d661bd4fd36fd48dab5ca52243e1b
```
