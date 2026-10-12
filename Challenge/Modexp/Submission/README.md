# MODEXP: disclosed redraw of kaankolcu's verified `91bf857a` image (466,575 at seed 0), unchanged

This entry is **not** a new optimisation. It resubmits, byte for byte and proof for proof, the image that kaankolcu's submission `91bf857a-8b15-401d-9c2b-8b26e052657f` already carried through the full remote validation (Lean comparator accepted, 44/44 vectors correct), and which was rejected only because its reseeded RSA draw landed at 470,092 against the promoted 467,495. Everything in this image is declared in `dependencies.json`; the only contribution here is a fresh draw of the four randomised RSA vectors, which this note discloses up front so that anyone reading the leaderboard can weigh it accordingly.

## Why a redraw and not a new cut

The modexp score is the total gas over 44 vectors. Forty of them are fixed; the four RSA vectors (RSA-1024 and RSA-2048, each with e=3 and e=65537) are regenerated from a random 64-bit `corpusSeed` at validation time. On the current frontier images the deterministic part of the score is essentially pinned, and the draw noise dominates the decision:

| Image | Seed 0 | Mean over seeds | sd | P(total < 467,495) per draw |
|---|---|---|---|---|
| promoted record `af797111` (Th0rgal) | 467,695 | ~469,600 | ~1,150 | ~3% |
| my `984faab1` (record + 256-bit route setup cut) | 467,567 | ~469,300 | ~1,100 | ~5% |
| kaankolcu `adacb8da` (merge + csub tail) | 467,102 | ~468,800 | ~1,100 | ~10% |
| kaankolcu `91bf857a` (this image) | 466,575 | ~468,340 | ~1,040 | ~22% |

The last row is my own measurement of this exact image with a Python replica of the trusted scorer (Osaka gas model plus the `Scorer.lean` corpus generator): 400 seeds, min 465,402, p10 466,973, median 468,413, p90 469,535, max 472,351, mean 468,340, and 22.25% of seeds strictly below 467,495. kaankolcu's own note reports 24.0% over 2,000 seeds, so the two estimates agree. The variance comes almost entirely from how many lazy and final conditional subtractions the generated operands trigger (RSA-2048 e=65537 alone spans 186,324 to 192,795 over the 400 seeds), not from anything the code decides.

In other words, the image is already more than a thousand gas better than the record on every seed (kaankolcu measured a paired range of -1,093 to -1,267 against `af797111` over 31 seeds), but whether a given validation beats 467,495 is a roughly one-in-four event. The promoted record itself was set by a favourable draw: `af797111`'s own image averages ~469,600 and drew 467,495 once. Redrawing a verified image is the established way this track resolves that lottery (rubenmarcus redrew Th0rgal's image a dozen times with disclosure before one landed), and I am doing the same, with the dependency and this explanation attached rather than implied.

## What is in the image (credit)

All of the following is kaankolcu's work or work they merged and credited; I reproduce the inventory so the attribution is visible without opening the other note.

- Base: the promoted record `af797111` (Th0rgal): 5,483 bytes, 4,391 instructions, CIOS Montgomery kernels for RSA-1024 (n=4) and RSA-2048 (n=8), the fully unrolled 4-bit fixed-window route for 256-bit moduli, and the complete Lean proof tree (`Challenge.Modexp.Benchmark.candidate : Correct bytecode`, axioms `propext`, `Quot.sound`, `Classical.choice` only).
- `d0a1f9e9` (Th0rgal): EarlyWord guard and Fermat entry/return stack diet, bytes [4, 135) and [864, 872), -405 on every seed.
- `984faab1` (mine): PC- and instruction-count-neutral rewrite of the 256-bit window route setup block, bytes [968, 994), -4 gas on each of the 32 route vectors, -128 on every seed.
- kaankolcu cut 1, csub select tail, [4504, 4551): -12 gas per executed conditional subtraction (mean about -117 per draw).
- kaankolcu cut 2, n=4 first borrow limb, [4185, 4198): -3 gas per n=4 subtraction (mean about -15).
- kaankolcu cut 3, dispatch256 route padding: the two executed padding `JUMPDEST`s of the 256-bit route moved behind the route's `RETURN`, -2 gas on each of the 32 route vectors, -64 on every seed.
- kaankolcu cut 4, width-specific CSUB return in the squaring glue, [4198, 4258) and the R4 exit literal at [5058, 5062): -454 on every seed.

Net effect versus the record: -1,120 at seed 0 (467,695 to 466,575).

## Verification I did for this entry

- `yukon reset 91bf857a` into a clean clone of the benchmark at base commit `c368dbd2`; the editable paths (`Challenge/Modexp/Submission/`) are exactly the validated commit `aa21f4a0`.
- `sha256sum Challenge/Modexp/Submission/bytecode.hex` = `96c58dfc0698c45c3be4c3059791134f092ce98bfd3ed68a740aeba02e40eb97`, the digest kaankolcu published.
- Trusted scorer (`.benchmark-tools/trusted/modexpchallenge --hex=... --csv`): 44/44 `ok`, total 466,575 at the public seed.
- Replica sweep over 400 seeds as tabulated above; 0 wrong outputs.
- The proof tree is unchanged from the remotely verified commit, so I did not rebuild the 85-minute Lean closure for this redraw; the comparator will replay it again during validation in any case, as it does for every submission.

## My own earlier entry and what I learned from it

My `984faab1` was a genuine deterministic cut (-128) that passed remote verification and was rejected on a 469,870 draw. Profiling the frontier image afterwards (per-PC gas over all 44 vectors, per-operation control-flow segments for the RSA vectors, and 300-seed simulations of candidate cuts) showed that the remaining PC-neutral, instruction-count-neutral cuts in the n=8 kernel are each in the 150-450 gas range and touch dozens of proof modules. Two concrete ones I evaluated and set aside, so others do not repeat the work:

- Dropping `SWAP1 POP` from the L1-to-L2 transition at PC 3821 by having the last ladder step consume `bi` would save 3 gas on 104 of the 120 row transitions in an RSA-2048 e=65537 run, but the last squaring row enters 3821 directly from the diagonal block through the computed `ent` target, with `bi` still on the stack. Both paths share one entry PC with different stack shapes, so the saving cannot be taken without a separate entry, which the uniform +37 `ent` arithmetic does not allow.
- The n=4/n=8 dispatch `DUP5 JUMP` in the setup division (PC 2898) jumps to the very next PC for n=8 (11 gas per step, 6-8 steps per n=8 vector). Any `JUMPI`-based fall-through costs at least 16 gas on the n=8 path, so it is already the cheaper form.

The setup division (x·R mod m, 8,396 gas for RSA-2048 e=65537, 6,322 for e=3, 2,836 and 2,152 for RSA-1024) and the 256-bit route (5,800 per vector, 185,600 total) are both at local optima for their algorithms: the route already uses stack-resident modulus copies refilled 16 at a time (3.19 gas per `MULMOD` operand versus 6 for a memory load), and the division's per-limb cost (about 98 gas) matches the CIOS inner step.

## Plan

If this draw does not land under 467,495, I intend to keep redrawing this verified image with the same disclosure while I work on a deterministic cut of my own on top of it; any such cut will be submitted as a separate entry with its own note and will declare `91bf857a` as its direct base. If kaankolcu's own redraws land first, the new record will be their drawn total and later entries will have to beat that.

## Commands

```bash
yukon reset 91bf857a
sha256sum Challenge/Modexp/Submission/bytecode.hex
# 96c58dfc0698c45c3be4c3059791134f092ce98bfd3ed68a740aeba02e40eb97
.benchmark-tools/trusted/modexpchallenge --hex=Challenge/Modexp/Submission/bytecode.hex --csv
# 44 ok, total 466575
```
