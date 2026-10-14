# MODEXP: our abbf9bf4 plus the n=4 squaring group, newton-batch and zneg2 (457,253 at seed 0)

Work by Claude Opus 5.5 agents in Claude Code, one per lane. A short OpenAI Codex continuation ran replica sweeps and dependency builds during an account switch.

This extends our `abbf9bf4` (stack-v10c, n8grpt, the current record at 460,289). Everything in `abbf9bf4` is in this image. It adds our n=4 squaring kernel group from `d62773b1` (`n4a`, `n4f`, `n4t`, `rare4`), our `newton-batch` from `92ac47cf`, and two new cuts, `zneg2` and `dead3383`. No cut in this image comes from another solver's submission beyond the credited ancestry listed below.

## Context and goal

Minimise total gas over the 44 scorer vectors while `Correct bytecode` stays proved for the exact bytes. Direct base: our `abbf9bf4`, 5,531 bytes, 4,364 instructions, 458,608 gas at seed 0. This image has 5,544 bytes and 4,413 instructions: 457,253 gas at seed 0, 1,355 below. The generated `Artifact.lean` fails when S (distinct bytes per 64-byte chunk, summed) plus L (code length) plus 8 per chunk exceeds 8,194. This image: S 1,924, L 5,544, 87 chunks, so 8,164, 30 below the limit.

## Setup

- Source `Layr-Labs/eip8200-challenges` at `3db491e`. Lean `v4.31.0`.
- Gas: a Python replica of the scorer (Osaka gas plus a port of `Scorer.lean`'s corpus generator). It matched official per-vector gas on public runs, the Lean scorer on every benched seed, and the official runs of our earlier submissions on all 44 vectors.
- Proof check: a full `lake build Challenge.Modexp.Submission.Solution` of these exact bytes.

## The cuts

- **n4a.** In the n=4 kernel the squaring result `t` lives on the stack and is stored at 0x840..0x8a0 at the end of each squaring. The next squaring reads its operand `a` from there, so the squaring-to-squaring `MCOPY` is skipped.
- **n4f.** The n=4 squaring tail falls through into the counter block, its only predecessor, so `PUSH2 JUMP JUMPDEST` goes (12 gas per n=4 squaring).
- **n4t.** The n=4 squaring tail tests `tn` from the stack before the counter and jumps straight to the next first row. The rare `tn != 0` case has its own block.
- **rare4.** If `tn != 0` at the n=4 tail, a block subtracts `N` from the four `t` limbs in place on the stack, zeroes `tn` and jumps back to the stores, instead of the shared subtraction, select and `MCOPY` detour.
- **newton-batch.** The RSA setup no longer computes the negated low-limb inverse with its own 49-instruction Newton chain. The dinv site calls one shared Newton subroutine on `p = dodd * n0` and derives both inverses from `x = newton(dodd * n0)` (`newton(a * b) * b = newton(a)`; `n0` and `dodd` are odd on this route). -84 gas on each RSA vector.
- **zneg2.** The row pointer counts up through negative values (`q' = -q`), so the row tail step is `PUSH1 20 ADD` instead of a 33-byte `PUSH32 -32 ADD`. Address computations become subtractions (`0xe0 - q`, `0x920 - q`, `0x820 - q`), and setup tests n=4 by `q' + 0x80 == 0`. It is mainly a budget lever (+3 gas per row-pointer reset) that pays for the n=4 group under the artifact limit.
- **dead3383.** The dead multiply-preclear entry at 3383, whose only jumper was the trampoline removed by `dead5466`, is deleted. 0 gas, budget only.

## Proof changes

- The n=4 proofs (`R4Blocks`, `R4Runs`, `R4Trace`, `R4Hooks`, the n=4 section of `SquareLoop`, `TnM128SquareExit`, `Cios2Dispatch`) come from `d62773b1`'s tree through a three-way merge against `5788127e`, with `abbf9bf4`'s n=8 kernel files kept.
- newton-batch: `Setup`, `ShiftPaths`, `ShiftStates`, `ShiftTrace1/4/5`, `ShiftCorrect`, `RootE3*` and the `ShiftModel` Newton algebra lemmas, as in `92ac47cf`.
- zneg2: `TnCacheRowPointers.qptr n i = ofNat (2^256 - 32(n-i))` with new `qptr_end`, `sub_qptr` and `sub_qptr_toNat`. The row tail, multiply head (`bAddr q = 0xe0 - q`), square diagonal, first row, product setup, square exit and the `R4Hooks` H1 test carry the subtraction addresses.
- 57+ more files only renumber pcs, indices or memory offsets. Apart from `README.md` and `dependencies.json`, the tree differs from `abbf9bf4` in 95 modified files (94 Lean files and `bytecode.hex`) and one deleted dead file, `R4SquareScratchAgreement`. `Solution.lean` is unchanged.

## Cuts merged from other submissions (credited, declared)

| Submission | Author | Bytes | Change | Gas, every seed |
|---|---|---|---|---|
| `d0a1f9e9` | Th0rgal | [4, 135), [864, 872) | EarlyWord guard; Fermat entry/return stack diet | -405 |
| `984faab1` | UsamaInayat | [973, 994) | 256-bit window route setup block | -128 |

Both entered through `bdd36736` and are inherited through `abbf9bf4`; later routes superseded those exact bytes and kept the checks.

## Results

Python replica, 44 vectors, 0 wrong outputs in every sweep:

| Sweep | Image | Mean | sd |
|---|---|---|---|
| seed 0 + 30 seeds of `random.Random(8200)` | `abbf9bf4` (record) | 460,436.9 | 1,074.4 |
| | **this image** | **458,873.6** | 944.7 |
| 1,000 fresh seeds of `random.Random(202610140702)` | `abbf9bf4` (record) | 460,294.4 | 1,027.0 |
| | **this image** | **458,781.9** | 941.9 |

- Paired against `abbf9bf4`: -1,563.2 mean on the first sweep and -1,512.5 on the 1,000-seed sweep, every seed negative (range -2,062 to -1,151).
- A differential fuzz of these exact bytes against `pow` found 0 wrong in 603 completed adversarial inputs (n=4 and n=8 moduli, near-modulus, all-ones, 0/1/2 bases, even and power-of-two moduli, odd widths, truncated calldata, targeted at the new n=4 and zneg2 blocks). 309 more ran past the replica's step cap and are not counted.
- The official run draws its own random corpus seed: 950 of 1,000 fresh replica seeds scored below 460,289.

## Commands

```bash
lake build Challenge.Modexp.Submission.Solution    # full proof build of the exact bytes
sha256sum Challenge/Modexp/Submission/bytecode.hex
# 796161fc3dacc4fb8c35e0b6f1e9873316c0ebe066604d88ff7c5d284a3f34d1
```
