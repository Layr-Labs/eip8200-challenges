# MODEXP v15: q7 lifetime cache in the spent inverse slot

The candidate uses **392,214 gas** on the 44 seed-zero vectors, **340 gas less**
than the promoted v14 source at 392,554. The executable remains 10,915 bytes
and 8,722 instructions. The two RSA-2048 cases improve by 20 and 320 gas;
the other 42 cases are unchanged.

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

V15 observes that the low-limb inverse has its last use in column 8. Its stack
slot then caches quotient q7 (memory word 1280) through columns 9--15, replacing
fourteen memory reads with stack duplicates. Column 16 restores the inverse
from memory before the footer can observe the frame. Cache installation and
restoration cost 22 gas, while the fourteen replacements save 42, for a net
20 gas per kernel invocation. The seed-zero corpus invokes the kernel once in
`rsa2048_1` and sixteen times in `rsa2048_2`, yielding the measured 340 gas.

The latest leader's compatible window, table, and four-word squaring changes
contribute another 633 gas relative to v13. Its first-product output order
allows the 57-gas consumer in column zero, saving another 51. Together with
the v14 and v15 lifetime changes, this saves 1,976 relative to v13's 394,190.

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

The v15 artifact passes every official emulator vector and a 20-seed replay,
with no wrong output or gas regression. The proof checks the exact bytecode,
including the cached-state lifetime, each affected column, frame restoration,
and all shifted control-flow targets.
The seed-zero comparison is paired; official scores can use a different seed.

Decoded executable SHA-256:
`b27398baf1958a084cd6453fb4c3baebc72c34205c04037b3f13036a5e769038`.

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
and supporting search/validation work with GPT-6 Astra / Codex. This v15 adds
the post-column-8 q7 cache, restoration handoff, proof integration, and
validation by Codex.

The complete inherited provenance is in `dependencies.json`. Apache 2.0
licensing and upstream notices are preserved.
