# MODEXP v15: in-domain overflow handler for the eight-digit squaring loop

This submission keeps every byte of the promoted v14 image (`de134b66`, commit
`3297ede5`) except two places: the target of the squaring footer's overflow branch
(one `PUSH2` immediate at pc 8141) and the dead `PUSH0`/`PUSH1 00` sled at pc 8324..8799,
which now holds a 198-instruction (286-byte) overflow handler. The sled keeps its 476 bytes and
384 instructions, so no other pc or instruction index moves.

## What changes

The eight-digit mixed-radix Montgomery squaring loop (pc 5858) produces
`T = (A² + M·N)/R` with `T < R + N`. When `T ≥ R` (the "overflow" flag at 0x6e0 is
nonzero), v14 leaves the mixed-radix domain: it converts the column words to 256-bit
limbs (pc 8800), subtracts `N` on limbs (pc 4037), copies the result and re-enters the
kernel through the conversion at pc 5615. That round trip costs about 849 gas more than
an ordinary iteration, and the RSA-2048 `e = 65537` vector meets it about three times per
corpus draw on average (never on seed 0).

The handler at pc 8324 does what the ordinary footer does — counter test, decrement,
repack of the column words into the nine 244-bit digits at 0x300..0x400, jump to 5858 —
and subtracts the modulus digits (already on the stack) while repacking. Each borrow is
the sign bit of the 256-bit difference word. When the counter is zero (overflow on the
last square) it jumps to pc 8800 exactly as before, so that path is unchanged.

| | v14 | v15 |
|---|---:|---:|
| Seed-0 score | 392,554 | 392,554 |
| Mean over 1,000 official-corpus seeds | 395,417 | 393,452 |
| Paired mean delta | | −1,965 |
| P(score < 392,726) | 0.038 | 0.174 |
| P(lower than v14 on the same seed) | | 0.950 |
| Worst paired delta | | +23 |

The +23 case is an overflow on the last square only: the handler's counter test costs
23 gas before jumping to the unchanged exit.

Decoded executable SHA-256 (v15):
`d4b3fb3af0afe234f09feec9fac1738bd855feb869de9cc3ca6ca26a88989141`. The v14 section below keeps the parent's hash.

## Proof map (new and changed)

- `Proofs/CRT/OverflowHandlerExecution.lean` (generated): the handler's two straight-line
  programs, their symbolic models, part-wise `simp` run lemmas and control lemmas, in the
  same style as `CRTKernelExecution.lean`.
- `Proofs/CRT/OverflowHandlerArith.lean`: the 244-bit borrow step on 256-bit words
  (`sub_step`, `top_step`) and `sub_digits`, which telescopes the borrows with
  `MixedMontgomery.carryTelescopes` and reads the digits of `Q − N` back.
- `Proofs/CRT/OverflowHandlerMeaning.lean`: `handlerMemory` in cell form,
  `handler_model` (generated model = cell form), `handler_represents` (the new digits
  represent `Q − N` when `R ≤ Q < R + N`), counter and liveness facts.
- `Fast/CRTArtifactBlocks.lean`: the handler's four artifact blocks and `validJump8324`.
- `CRT/CRTKernelExecution.lean`, `CRTControl.lean`, `CRTGasSteps.lean`,
  `CRTGasStepsNormalized.lean`, `CRTLoopFrames.lean`: the overflow branch targets 8324;
  gas-step and normalization lemmas for the handler.
- `CRT/PureLoop.lean`: `next` uses `handlerMemory` on overflow; `one_round` uses
  `handler_represents`. `LoopInvariant`, `CRTLoopInduction`, `CRTLoopOperations`,
  `CRTLoopRouting`, `CRTLoopComplete`: the overflow round runs the handler and loops; the
  last round reaches 8800 through the handler's counter test.
- `CRT/CRTOverflowMore.lean` is removed (the old re-entry route is no longer used by the
  loop).

All inherited attribution (the v14 text below, `dependencies.json`, `REUSE_PROVENANCE.md`,
`REDRAW.md`) is kept unchanged.

---

# MODEXP v14: cancelled carries and temporary quotient caches

The candidate uses **392,554 gas** on the 44 seed-zero vectors, compared with
**402,533** for Th0rgal's promoted `0498a927-e9d9-41a2-8737-4315d8059b5c`:
**9,979 gas (2.48%) saved**. The executable contains 10,915 bytes and 8,722
instructions. Two scored cases improve and 42 are unchanged.

## Arithmetic and scheduling

The retained mixed-radix Montgomery kernel uses eight 244-bit digits and a
96-bit top digit, preserving the 2^2048 Montgomery factor. Each column tracks
an ordinary word residue and a residue modulo P = 2^251 - 1.

The v13 arithmetic foundation recovers general carries with
`ADDMOD(H, NOT(lo), P) >> 5`. In the first eight columns, cancellation makes
the total S divisible by B = 2^244 and the carry S/B smaller than P. Since
B * 128 is congruent to 1 modulo P, that carry is `MULMOD(H, 128, P)`.
This removes the general reconstruction and a low product whose result is
unused. The ninth, 96-bit cancellation digit retains general recovery.

V14 extends the leader's last-use and producer/consumer scheduling approach
to temporary storage across columns:

- Before modulus digit n8 is first needed, its stack slot holds quotient q0.
  Column 8 restores n8 while consuming q0 in its final multiplication.
- After column 8 uses modulus digit n0 for the final time, its slot holds q8
  through columns 9–16. The last n0 multiplication and cache installation
  are jointly scheduled. Column 16 restores n0 while consuming q8.

The scratch stores remain intact. Every original modulus slot is restored
before a footer branch or a new iteration. Compared with the previous combined
prototype, the caches save 56 gas per kernel invocation, or 952 over 17 calls.
The terminal-product schedule costs 43 gas, including cache installation,
compared with 40 for the original product and 11 for a separate installation.

The latest leader's compatible window, table, and four-word squaring changes
contribute another 633 gas relative to v13. Its first-product output order
allows the 57-gas consumer in column zero, saving another 51. Together with
the lifetime changes, this saves 1,636 relative to v13's 394,190.

## Proof map

`RoundedCRT.lean`, `RoundedWordBridge.lean`, and `CancelledCRT.lean` establish
the carry identities and their bounds. `LifetimeCache.lean` describes which
stack slot holds a quotient at each stage. The seventeen `CRTColumnExecution`
modules prove the exact new instructions and their relation to the unchanged
semantic column models. `CRTKernelExecution.lean` composes those results and
preserves the modulus memory reads used for restoration. The loop invariant
supplies the required equality between cached modulus digits and memory.

`KernelRefinement`, the column arithmetic/contracts, the loop modules, and the
caller adapters connect execution to modular exponentiation. `Bytes.lean`,
`TnM128CandidateArtifact.lean`, and `bytecode.hex` bind the proof to the actual
executable. The acceptance theorem is `Challenge.Modexp.Benchmark.candidate`.
It covers every valid challenge input given sufficient gas, including padded
short inputs and operand lengths through 1,024 bytes.

## Reproduction and measurements

Use the challenge's current entry points:

```sh
./setup.sh modexp
./benchmark.sh modexp
```

The documented local execution mode is
`BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh modexp`. Comparator and the independent
Lean kernel check the exact protected bytecode. Permitted axioms are `propext`,
`Quot.sound`, and `Classical.choice`. The research repository stores the acceptance
receipt, reproducible search scripts, source inventory, and broader finite tests.

The final prototype's ten-seed/edge replay has 555 jointly correct completed
cases and 65 shared execution caps, with no observed wrong outputs, completion
regressions, or gas regressions among completed cases. A separate 256-case
whole-kernel comparison checks identical scratch memory and the complete
output frame, including extreme and randomly chosen full-width words.
The seed-zero comparison is paired; official scores can use a different seed.

Decoded executable SHA-256:
`4eacbda6cbedd96b828f2cf94f9c072e33fb5923d294622dfb53dbf0507b02c5`.

## Attribution

Claude found the original optimization in aerugo-ef's repository. Subsequent
Codex work builds on that foundation and the credited public implementations.
Aerugo-ef v9 supplies the retained mixed-radix architecture and proof
infrastructure; local v12/v13 supply scheduling, redundant-mask elimination,
rounded carry recovery, and cancelled-digit recovery.

Th0rgal's public v10/v11/v12/latest improvements are credited to Gemini 3.1 Pro /
Antigravity. The latest compatible window, table, four-word schedules and
first-product ordering are reused here. This v14 adds the cross-column cache
lifetimes, consumption/restoration handoffs, their full proof integration,
and supporting search/validation work with GPT-6 Astra / Codex.

The complete inherited provenance is in `dependencies.json`. Apache 2.0
licensing and upstream notices are preserved.
