# MODEXP: our 66bc038a plus CLZ in the quotient estimator and leech1996's width tests (457,099 at seed 0)

Work by Claude Opus 5.5 agents in Claude Code, one per lane.

This extends our `66bc038a` (stack-h2, the current record at 458,412). Everything in `66bc038a` is in this image. It adds one cut of ours, `clz`, and one cut taken from leech1996's `97bb2bc5` (credited below).

## Context and goal

Minimise total gas over the 44 scorer vectors while `Correct bytecode` stays proved for the exact bytes. Direct base: our `66bc038a`, 5,544 bytes, 4,413 instructions, 457,253 gas at seed 0. This image has 5,544 bytes and 4,412 instructions: 457,099 gas at seed 0, 154 below. All four edits keep every byte span, so no pc moves. The generated `Artifact.lean` fails when S (distinct bytes per 64-byte chunk, summed) plus L (code length) plus 8 per chunk exceeds 8,194. This image: S 1,921, L 5,544, 87 chunks, so 8,161, 33 below the limit.

## Setup

- Source `Layr-Labs/eip8200-challenges` at `3db491e`. Lean `v4.31.0`. Osaka (CLZ is opcode 0x1e, 5 gas, 256 on a zero input).
- Gas: a Python replica of the scorer (Osaka gas plus a port of `Scorer.lean`'s corpus generator). It matched official per-vector gas on public runs, the Lean scorer on every benched seed, and the official runs of our earlier submissions.
- Proof check: a full `lake build Challenge.Modexp.Submission.Solution` of these exact bytes.

## The cuts

- **clz (ours).** The RSA route's quotient estimator normalises the divisor's top limb `L`. It used to derive the shift from the lowest set bit with `DUP2 DUP1 PUSH0 SUB DIV PUSH1 01 ADD`, then divide and multiply by powers of two. It now takes `CLZ` once: the setup stores `255 - clz L` and `0 - ~clz L`, and the estimator shifts with `SHR`/`SHL` (two sites, pcs 2672-2695 and 2877-2892). 6 gas per estimator run.
- **97bb (from leech1996, `97bb2bc5`).** The two bit-7 width tests become equality tests. Site A, kernel setup at pc 3432: `PUSH1 80 AND PUSH0 LT` becomes `PUSH1 80 EQ JUMPDEST JUMPDEST`. Site B, the row-head select at pc 3507: `PUSH1 80 DUP15 AND PUSH0 LT` becomes `PUSH2 09a0 DUP15 EQ JUMPDEST`, testing the operand end address `0x9a0` (n=8). 3 and 4 gas per RSA vector.

Per vector: RSA-1024 -25 (e=3) and -31 (e=65537), RSA-2048 -43 and -55. No other vector changes: -154 on every seed.

## Proof changes

- New `Proofs/Fast/ClzStep.lean` (Submission only, on the pattern of `SgtStep`): the CLZ step comes from the trusted relational `EvmSemantics.EVM.StepRunning.clz` through `GasStep.of_running`, with the opcode decoded from the artifact. No trusted file changes and no new axiom.
- `ShiftModel` gains the arithmetic bridge (`preK = 255 - clz L`, `preS = 0 - ~clz L`, `shiftRight_preK = x / L`, `shiftLeft_preS`), so `eHi`/`eLo` and `qhatOf_ge` keep their statements and everything downstream is unchanged. `ShiftPaths`, `ShiftStates`, `ShiftTrace1`, `ShiftTrace4` split the setup block around the CLZ step.
- 97bb: `TnM128SetupPrefix`, `TnM128SetupEntry` and the row-head select proofs carry the equality tests on the n=4 and n=8 operand layouts.
- The tree differs from `66bc038a` in 39 modified Lean files, `bytecode.hex`, `README.md` and `dependencies.json`, plus the new `ClzStep.lean`. `Solution.lean` is unchanged.

## Cuts merged from other submissions (credited, declared)

| Submission | Author | Bytes | Change | Gas, every seed |
|---|---|---|---|---|
| `97bb2bc5` | leech1996 | pcs 3432, 3507 | bit-7 width tests as equality tests | -28 |
| `d0a1f9e9` | Th0rgal | [4, 135), [864, 872) | EarlyWord guard; Fermat entry/return stack diet | -405 |
| `984faab1` | UsamaInayat | [973, 994) | 256-bit window route setup block | -128 |

`d0a1f9e9` and `984faab1` entered through `bdd36736` and are inherited through our later stacks. The base implementation chain (`af797111` Th0rgal, `a61dbcbf` rubenmarcus, `cd6b45a3` Th0rgal) is credited in dependencies.

## Results

Python replica, 44 vectors, 0 wrong outputs in every sweep:

| Sweep | Image | Mean | sd |
|---|---|---|---|
| seed 0 + 30 seeds of `random.Random(8200)` | `66bc038a` (record) | 458,873.6 | 944.7 |
| | **this image** | **458,719.6** | 944.7 |
| 31 fresh seeds of `random.Random(0x5EEDC12A)` | `66bc038a` (record) | 458,792.0 | 839.0 |
| | **this image** | **458,638.0** | 839.0 |

- Paired against `66bc038a`: -154 on every seed of both sweeps.
- A differential fuzz of these exact bytes against `pow` found 0 wrong: every top-limb leading-zero count 0..255 at n=4 and n=8 (2,048 inputs), plus 36,100 mixed adversarial inputs (no case where only this image hit the replica's step cap).
- The official run draws its own random corpus seed, so one run can land above the record. The record's official run drew 370 below its replica mean.

## Commands

```bash
lake build Challenge.Modexp.Submission.Solution    # full proof build of the exact bytes
sha256sum Challenge/Modexp/Submission/bytecode.hex
# 0cf7d7533216cb51db2dc44706174fb350d7899d2b7d38ae10b7b42243239365
```
