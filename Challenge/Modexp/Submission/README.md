# EIP-8200 MODEXP: stack-v10c = 5788127e (stack-v9) plus the n=8 squaring-kernel group and the 256-bit tail

Work by Claude Opus 5.5 agents in Claude Code, one per lane.

This extends our `5788127e` (stack-v9, the current record at 462,538), which is `1954e3f4` plus our N1 and P1 cuts. Everything in `5788127e` is in this image. It adds fifteen cuts of ours: `p2`, `zloop`, `zreset`, `m9rot`, `dead5466`, `tl`, `msplit`, `deadbytes`, `offsets`, `depad`, `n8g`, `rarej`, `st8`, `frq` and `t256`. No cut in this image comes from another submission.

## Context and goal

Minimise total gas over the 44 scorer vectors while `Correct bytecode` stays proved for the exact bytes. Direct base: our `5788127e`, 5,544 bytes, 4,359 instructions, 461,838 gas at seed 0. This image has 5,531 bytes and 4,364 instructions: 458,608 gas at seed 0, 3,230 below. `depad`, `deadbytes`, `dead5466` and `t256` change the code length, so most pcs after 2392 move. The generated `Artifact.lean` fails when S (distinct bytes per 64-byte chunk, summed) plus L (code length) plus 8 per chunk exceeds 8,194. This image: S 1,887, L 5,531, 87 chunks, so 8,114, 80 below the limit.

## Setup

- Source `Layr-Labs/eip8200-challenges` at `3db491e`. Lean `v4.31.0`; Comparator `v4.33.0-rc1`.
- Gas: a Python replica of the scorer (Osaka gas plus a port of `Scorer.lean`'s corpus generator). It matched official per-vector gas on 12,144 public runs, the Lean scorer on every benched seed, and the official runs of our earlier submissions on all 44 vectors.
- Proof check: a full `lake build Challenge.Modexp.Submission.Solution` of these exact bytes.

## The cuts

- **p2 and zloop.** The multiply and squaring row loops no longer carry the loop bound `pb` and the t-top address as separate constants. The frame holds the row pointer `q` (the loop exits when `q` reaches 0, so the tail is `DUP1 DUP3 JUMPI`) and `n1` in the bound slot. The squaring diagonal reads `a_i` from `mem[q + 0x920]`.
- **zreset.** At the exit of a row loop the row pointer is exactly 0, so that value is the carry-cache reset `tn := 0` and the separate push goes.
- **m9rot.** The M9 loop tests its counter at the bottom instead of the top. Entry counters are `n` or `n >> k`, always at least 1.
- **dead5466.** The generic preclear trampoline [5466, 5483) is deleted. Its only predecessor was a statically dead block.
- **tl.** The `tl` frame slot (the t-top address, 0x920 on every n=8 path) holds `n0 = mem[0xe0]`. The n=8 heads read `n0` with `DUP15`; setups read `tl` from memory.
- **msplit.** One multiply loop per width with constant t-top addresses. The n=8 head falls through into the Duff base, the n=4 head has its own copy, and the multiply setup computes the head per width.
- **deadbytes.** Statically unreachable filler inside the kernel is deleted (budget only).
- **offsets.** Computed-jump offset constants become label expressions. 0 gas.
- **depad.** Every `PUSHn` with leading zero bytes shrinks to its minimal width. 0 gas; the saved bytes pay for the other cuts under the artifact limit.
- **n8g.** The n=8 squaring exit glue: a new block tests `tn` from the stack (`SWAP12` also resets the slot), does the `t` to `a` `MCOPY` with constants and the counter test, and jumps straight to the next first row or the multiply setup.
- **rarej.** The `tn != 0` continuations jump straight into the width's subtraction (a new `JUMPDEST` for n=8), skipping the memory re-test and the width test.
- **st8.** The `tn` store moves past the mode `JUMPI`; only the multiply and final fall-through need it. The rare n=8 continuation stores a nonzero word for the select.
- **frq.** In the n=8 first row `q` is 0x100 on every entry, so `a_0 = mem[0xa20]` by constant (6 gas per n=8 squaring).
- **t256.** The 256-bit route's last windows (a tail whose only predecessor is the jump at 2391) move inline at 2388. -12 gas per 256-bit vector. The five dead `JUMPDEST` pads at 2392 to 2396 go.

Paired against `5788127e` the whole image saves 3,191 to 3,197 gas on average, and 3,087 to 3,230 on every one of the 62 seeds measured.

## Proof changes

- The n=8 squaring round has its own memory model (`SquareRoundC`, new): the round no longer flushes `tn` to 0x820, and the rare `tn != 0` path stores a nonzero word there for the select. `SquareLoop`, `TnM128SquareExit`, `TnM128SquareFinishSteps`, `TnM128SquareRowSteps` and the cache-trace files carry the new frame (row pointer `q`, `n1` and `n0` in frame slots) and the new exit blocks; `TnM128FusedEntry` has the per-width multiply setup; `CsubCore` splits the select tail for the nonzero-flag continuation.
- `Exp.Subroutines.monpro` is removed. No consumer used it (dead5466 deletes its trampoline). Five dead files are deleted: `CarryEntryLemmas`, `CarryFullFast`, `CarryFullSpecializedEight`, `CarryFullSpecializedFour` and `TnM128FusionFrame`.
- 57 more files only renumber pcs, indices or memory offsets. The tree differs from `5788127e` in 139 files in all (133 changed, 5 deleted, 1 new). `Solution.lean` is unchanged.

## Cuts merged from other submissions (credited, declared)

| Submission | Author | Bytes | Change | Gas, every seed |
|---|---|---|---|---|
| `d0a1f9e9` | Th0rgal | [4, 135), [864, 872) | EarlyWord guard; Fermat entry/return stack diet | -405 |
| `984faab1` | UsamaInayat | [973, 994) | 256-bit window route setup block | -128 |

Both entered through `bdd36736`; our C2 prologue and precopy256 route later superseded those exact bytes and kept the checks. The cuts that make up `5788127e` are listed in its own note: csub select tail, route padding, rsa-setup cuts 1 and 3, sqglue 1 and 2, layout-v1, csub2, precopy256, B4, C2, e3skip, N1 and P1.

## Results

Python replica, 44 vectors, 0 wrong outputs of 1,364 runs for both images in each sweep:

| Sweep | Image | Mean | sd |
|---|---|---|---|
| seed 0 + 30 seeds of `random.Random(8200)` | `5788127e` (record) | 463,628.4 | 1,065.8 |
| | **this image** | **460,436.9** | 1,074.4 |
| 31 fresh seeds of `random.Random(20261015)` | `5788127e` (record) | 463,366.1 | 1,093.8 |
| | **this image** | **460,169.6** | 1,111.2 |

- Paired against `5788127e`: -3,191.5 mean on the first sweep and -3,196.5 on the second, every seed negative (range -3,230 to -3,087).
- A differential fuzz of these exact bytes against `pow` found 0 wrong of 2,050 completed inputs: 1,500 2048-bit moduli with e = 3 and 65,537 (random odd, near 2^2048 and 2^2047 plus small, bases below, near and above the modulus; 1,948 visits to the new rare `tn != 0` block), 500 1,024-bit moduli, and 50 mid-width inputs (950 more generic-width or leading-zero-limb inputs ran past the replica's step cap and are not counted).
- Proof status: full Lean `Solution` build PASS on these exact bytes (exit 0, 2,327 jobs; `Challenge.Modexp.Benchmark.candidate` depends on axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`). Comparator and official-scorer run of these exact bytes: not run before sending.
- The official run draws its own random corpus seed, so a single run can land above the record: about 98% of draws are below 462,538 on the normal approximation of the 62 seeds.

## Commands

```bash
lake build Challenge.Modexp.Submission.Solution    # full proof build of the exact bytes
# replica sweep; our script, not in the archive
python3 multisweep.py v9=5788127e.hex v10c=Challenge/Modexp/Submission/bytecode.hex
sha256sum Challenge/Modexp/Submission/bytecode.hex
# 862e17e7636701a2cc995a7c5585645779bd67aa739bdd596cf78420ebe62298
```
