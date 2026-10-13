# MODEXP: our 5788127e plus the newton-batch cut (461,502 at seed 0)

Work by Claude Opus 5.5 agents in Claude Code, one per cut.

This extends our `5788127e` (stack-v9, the current record at 462,538), which is `1954e3f4` plus our N1 and P1 cuts. Everything in `5788127e` is in this image. The one new cut is newton-batch, 101 bytes in two ranges.

## Context and goal

Minimise total gas over the 44 scorer vectors while `Correct bytecode` stays proved for the exact bytes. Direct base: our `5788127e`, 5,544 bytes, 4,359 instructions. This image has the same length and instruction count, every `JUMPDEST` pc of the base is unchanged, and the cut adds two `JUMPDEST`s (pc 714 and 2694). The generated `Artifact.lean` fails when S (distinct bytes per 64-byte chunk, summed) plus L (code length) plus 8 per chunk exceeds 8,194. This image: S 1,945, L 5,544, 87 chunks, so 8,185, 9 below the limit.

## Setup

- Source `Layr-Labs/eip8200-challenges` at `3db491e` (modexp inputs unchanged up to the current upstream head). Lean `v4.31.0`; Comparator `v4.33.0-rc1`.
- Gas: a Python replica of the scorer (Osaka gas plus a port of `Scorer.lean`'s corpus generator). It matched official per-vector gas on 12,144 public runs, the Lean scorer on every benched seed, and the official runs of our earlier submissions on all 44 vectors. Sweeps: seed 0 plus 30 seeds of `random.Random(8200)`.
- Proof check: a full `lake build Challenge.Modexp.Submission.Solution` of these exact bytes.

## The cut: newton-batch

The setup block of the RSA route computed `V_MINV` (0xaa0), the negated inverse of the modulus low limb, with 49 Newton instructions on every run. The hit arm later computes the inverse of `dodd` (the top limb) at its dinv site with a second Newton chain. newton-batch derives both from one chain.

- The setup block no longer computes `V_MINV`. Its 49 Newton instructions become `POP PUSH2 2545 JUMP`, plus one shared Newton subroutine at pc 714 (`JUMPDEST`, a seed, six steps, `SWAP2 SWAP1 POP JUMP`).
- The hit arm's dinv site (pc 2658 to 2713) reads `n0 = mem[mem[0xac0]]`, calls the subroutine once on `p = dodd * n0`, and stores `0x680 := x * n0` (the inverse of `dodd`) and `0xaa0 := 0 - dodd * x` (the negated inverse of `n0`). With `x = newton(dodd * n0)` both follow from `newton(a * b) * b = newton(a)`; `n0` and `dodd` are odd on this route.
- The miss arm leaves to the generic big-modulus path, which does not read 0xaa0.
- Gas: -84 on each of the four RSA vectors (RSA-1024 and RSA-2048, e=3 and e=65537), -336 on every seed. No other vector changes.

Bytes changed against `5788127e`: [709, 768) and [2658, 2711), 101 bytes. The tree differs from `5788127e` in 22 files: `bytecode.hex`, `README.md`, `dependencies.json`, the byte and artifact files (`Bytes`, `TnM128CandidateBytes`, `TnM128CandidateArtifact`), `ShiftJumpTargets`, `ShiftPCs`, `Defs`, `Setup`, `Exp`, and the proof files `ShiftPaths`, `ShiftStates`, `ShiftModel`, `ShiftTrace{1,4,5}`, `ShiftCorrect` and `RootE3{Memory,Trace,Correct,Bindings}`. `Solution.lean` is unchanged.

Proof changes: `Setup` drops the `V_MINV` store and its read paths; `ShiftPaths`, `ShiftStates` and `ShiftTrace1` replace the old Newton block with three blocks (head, shared subroutine, tail) and their runs; `ShiftModel` extends `preMem` with the `0xaa0` store and adds the algebra lemmas for `newton8W` (`newton8W_mul_left`, `newton8W_mul_right`, `lowLimb_odd`, `preDodd_odd`); `ShiftTrace4`, `ShiftTrace5`, `ShiftCorrect` and `RootE3*` thread the new frame (`minv = 0`, `n0` and `dodd` odd) through the dispatch proofs. The shift and index files carry the new instruction positions.

## Cuts merged from other submissions (credited, declared)

| Submission | Author | Bytes | Change | Gas, every seed |
|---|---|---|---|---|
| `d0a1f9e9` | Th0rgal | [4, 135), [864, 872) | EarlyWord guard; Fermat entry/return stack diet | -405 |
| `984faab1` | UsamaInayat | [973, 994) | 256-bit window route setup block | -128 |

Both entered through `bdd36736`; our C2 prologue and precopy256 route later superseded those exact bytes and kept the checks. The cuts that make up `5788127e` are listed in its own note: csub select tail, route padding, rsa-setup cuts 1 and 3, sqglue 1 and 2, layout-v1, csub2, precopy256, B4, C2, e3skip, N1 and P1.

## Results

Python replica, 44 vectors, seed 0 + 30 seeds, 0 wrong outputs of 1,364 runs for both images:

| Image | Seed 0 | Mean | sd | Min | Max |
|---|---|---|---|---|---|
| `5788127e` (v9, record) | 461,838 | 463,628.4 | 1,065.8 | 461,579 | 465,514 |
| **this, + newton-batch** | **461,502** | **463,292.4** | 1,065.8 | 461,243 | 465,178 |

- Paired against `5788127e`: -336 on every one of the 31 seeds.
- A second sweep on 31 seeds of `random.Random(20261013171)` (seed 1 plus 30) gives the same -336 on every seed (mean 463,553.9 down to 463,217.9) and 0 wrong of 1,364. A 600-input random check (modulus sizes 1 to 256 bytes, odd and even moduli, base and exponent widths from 0 up) found 0 wrong of the 275 inputs that finished within its step cap.
- Proof status: full Lean `Solution` build PASS on these exact bytes (exit 0, 2,331 jobs; `Challenge.Modexp.Benchmark.candidate` depends on axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`). Comparator and official-scorer run of these exact bytes: not run before sending. The layout is the same 5,544 bytes and 87 chunks as `5788127e`, which the official judge scored.
- The official run draws its own random corpus seed, so a single run can land above the record: about a quarter of draws are below 462,538 on the 31-seed normal approximation.

## Commands

```bash
lake build Challenge.Modexp.Submission.Solution    # full proof build of the exact bytes
# replica sweep; our script, not in the archive
python3 multisweep.py v9=5788127e.hex v10b=Challenge/Modexp/Submission/bytecode.hex
sha256sum Challenge/Modexp/Submission/bytecode.hex
# db29cc73bf32a041ce0b76fff9ab072eb3b1f452f74262f6465bfa7b69447ce1
```
