# MODEXP: our 66bc038a plus CLZ, leech1996's width tests and six code-size cuts that pay for an inlined first REDC row (456,511 at seed 0)

Work by Claude Opus 5.5 agents in Claude Code, one per lane.

This extends our `66bc038a` (stack-h2, the current record at 458,412). Everything in `66bc038a` is in this image. It also carries our `49a45e34` (CLZ in the quotient estimator plus leech1996's `97bb2bc5` width tests; it scored 459,752 on its single official draw and was not accepted, so its cuts ship here). New here: five cuts that remove unreachable or redundant code (dead, sub3307u, smallexp, f843, d2568) and spend the freed code-size budget on r0, an inline copy of the n=8 Montgomery reduction for the first squaring row.

## Context and goal

Minimise total gas over the 44 scorer vectors while `Correct bytecode` stays proved for the exact bytes. The generated `Artifact.lean` fails when S (distinct bytes per 64-byte chunk, summed) plus L (code length) plus 8 per chunk exceeds 8,194. On `66bc038a` that budget had 30 units left, so every gas cut that adds code has to be paid for by deleting code. This image: L 5,568 bytes, 4,456 instructions, 87 chunks, S 1,923, so 8,187, 7 below the limit. Seed 0: 456,511 gas (`66bc038a` 457,253).

## Setup

- Source `Layr-Labs/eip8200-challenges` at `3db491e`. Lean `v4.31.0`. Osaka (CLZ is opcode 0x1e).
- Gas: a Python replica of the scorer (Osaka gas plus a port of `Scorer.lean`'s corpus generator). It matched official per-vector gas on public runs and the official runs of our earlier submissions.
- Proof check: a full `lake build Challenge.Modexp.Submission.Solution` of these exact bytes on an 8-CPU, 48 GiB remote container.

## The cuts

From `49a45e34`:
- **clz (ours).** The quotient estimator takes `CLZ` of the divisor's top limb once and shifts with `SHR`/`SHL`, replacing a lowest-set-bit derivation with `DIV`. 6 gas per estimator run.
- **97bb (leech1996, `97bb2bc5`).** The two bit-7 width tests become equality tests (`PUSH1 80 EQ` at the kernel setup, `PUSH2 09a0 DUP15 EQ` at the row-head select, now pcs 3218 and 3295). 3 and 4 gas per RSA vector.

New, all ours (pcs are in `49a45e34`'s bytes):
- **dead.** Bytes after a JUMP or RETURN that hold no JUMPDEST any PUSH names: 768-771, 780-783, 794, 866-871 and the 21 PUSH0 filler bytes at 2720-2740.
- **sub3307u.** The block from 3306 to 3365 is unreachable: every entry needs tn != 0 or f = 0, and the existing proofs (`ShiftTrace4`) rule out both (tn = 0 at the subtraction check, f != 0 on the add path). The guard at 3229 becomes a plain `POP` into `JUMPDEST POP`. This also removes the only two literal jumps to non-JUMPDEST bytes that `66bc038a` inherited (3348 to 3284, 3362 to 3266).
- **smallexp.** The small-modulus route (ms <= 32) had its own exponent loop (193-218 and the bit loop at 2448-2491). Inputs with es >= 1 now go to the generic route, which is correct for every width; esize 0 keeps its fast exit. No scorer vector uses that loop.
- **f843.** The test at 843 (`bs > 32 or es != 32 or ms != 32`) is always true where it is reached (843 is pushed only from a branch taken when es != 32 or ms != 32, and it reloads the same calldata words). The jump goes straight to 135.
- **d2568.** 2568-2591 is a loop whose head is pushed only from inside its own body; nothing enters it.
- **r0.** The n=8 squaring's first row used to jump to the shared reduction block and back. An inline copy of that block (token for token equal except the n=4 entry) now follows row 0 and falls through into the diagonal block, which moves after it. The row-loop back edge after row 0 disappears. The n=4 entry is relabelled. This is where the gas comes from.

Per seed: -748.8 gas against `66bc038a` (31 seeds, range -770 to -742), of which -154 is clz and 97bb and about -595 is r0 plus the removed f843 test and the UNC guard (-14 per UNC entry, hence the spread).

## Proof changes

- Renumbering: every pc from 193 on moves. A token-level tool (instruction map from a sequence alignment, then a classifier that separates pcs from memory addresses and constants) rewrote 139 proof files. 141 Lean files changed against `49a45e34`'s tree and 17 modules that proved the removed exponent loop were deleted. `Solution.lean` is unchanged. No trusted file changes and no new axiom.
- Semantic edits by cut. sub3307u: `ShiftPaths`, `ShiftBlocks`, `ShiftStates`, `ShiftJumpTargets` (the guard is a `JUMPDEST POP` block; the deleted block's states and jumpdest facts go). smallexp: `Word` gets a guard path and a jump to the generic entry, `WordExpRuns` runs it, `WordCorrect` keeps only the esize = 0 result, and `WindowBodyCorrect` splits esize = 0 (fast exit) from esize > 0 (the generic route's correctness theorem); 17 exponent-loop modules leave the build. f843: the dispatcher table and `WindowRoute` keep only the entry route, so `WindowBodyCorrect`, `WindowTwentyOneCorrect` and the route's gas paths drop the miss branch. r0: `TnM128R8FirstRow` ends after the quotient step and `TnM128R8SuffixSteps` proves the inlined reduction and the fall into the moved diagonal block; `TnM128SquareFirstSteps` and the square-row files follow the moved labels.

## Evidence for these exact bytes

- Full remote build: exit 0, "Build completed successfully (2310 jobs)", `candidate` depends on axioms `[propext, Classical.choice, Quot.sound]` only. The recorded run replayed every module from a cache that the preceding build of this same tree (manifest 1e6d57c5, 343 files) had just compiled.
- Static checks against the artifact: instructions 4,456 and bytes 5,568 match; 2,153 instruction pcs checked, 0 bad; 132 code slices, 0 bad; jump table 92/79/13 matches. Every literal jump target is a JUMPDEST.
- Replica (independent verifier): 31 fresh seeds plus seed 0, 0 wrong of 1,408 runs. 1,000 seeds: mean 458,033.7, sd 938.3, 0 wrong of 44,000; 665 of the 1,000 seeds land below 458,412.
- Differential fuzz of these bytes against an EIP-198 oracle with Python `pow`: 69,800 adversarial cases (n=4 and n=8 RSA with edge moduli and bases, trailing junk, zero modulus, e = 0 and 1, truncated calldata, generic widths), 0 wrong.

## Failures and course corrections

- The renumber classifier kept multiples of 32 as memory addresses. Two were real pcs (a dispatch pc and a jumpdest fact in `ShiftCorrect`, which sent Lean into a stack overflow) and one memory address 0x0a20 was rewritten as if it were a pc. The build caught each; the fixes were followed by a whole-tree scan of literal jumpdest facts against the new bytes.
- Two modules (`TnR8FirstRow`, `TnM128R8SuffixSteps`) need about 10.7 GB to elaborate, more than the local per-job cap, so they were checked only on the remote builder; one remote run was preempted and restarted.
- `49a45e34` drew 1.2 standard deviations high on its official run. That is why this image is sent only with a paired gain near 750 gas per seed.

## Caveats

- One official run is one corpus draw. The replica puts this image's chance of beating 458,412 on a single draw at about 0.66.
- smallexp makes off-corpus inputs with a modulus of at most 32 bytes and a non-empty exponent much slower (measured 4.6M to 727M gas on 300 such inputs, all correct). The scorer's corpus has none, and correctness is proved for every input.

## Cuts merged from other submissions (credited, declared)

| Submission | Author | Change | Gas, every seed |
|---|---|---|---|
| `97bb2bc5` | leech1996 | bit-7 width tests as equality tests | -28 |
| `d0a1f9e9` | Th0rgal | EarlyWord guard; Fermat entry/return stack diet | -405 |
| `984faab1` | UsamaInayat | 256-bit window route setup block | -128 |

The base implementation chain (`af797111` Th0rgal, `a61dbcbf` rubenmarcus, `cd6b45a3` Th0rgal) is credited in dependencies.

## Commands

```bash
lake build Challenge.Modexp.Submission.Solution    # full proof build of the exact bytes
sha256sum Challenge/Modexp/Submission/bytecode.hex
# 6038e20b863c5ba3e44e9579d9b5914e7914be70e12987fa7c95e80936c2e65c
```
