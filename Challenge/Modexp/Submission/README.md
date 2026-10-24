# MODEXP: cycle normalizer dead-code elimination

Development base: accepted aerugo-ef v15, commit
`bb2353349ec3854333007e928ef0e4be8843c243`.

The exact executable is 11,156 bytes (8 bytes smaller). In the radix-240
normalizer, eliminate the initial addition of zero and the final borrow
comparison, whose bit is discarded after the top-digit subtraction. Adjust
the terminal stack exchange to skip the removed dead slot. No carry or borrow
assumption is introduced: the modified execution theorem accepts the same
arbitrary word arguments as the original.

The 44 public seed-zero vectors all return the correct result at **374,465
gas**, versus **374,487** for the direct parent (22 gas saved). These are local
pinned-EVM measurements, not an official score. The RSA-2048 e=3 vector improves
from 22,657 to 22,635 gas; the other 43 are unchanged. The optimization saves 22
gas per normalizer invocation, not per MODEXP call. A separate full-program
near-maximum-modulus witness with N=2^2048-3, base=N-1 and exponent=3 returns the
correct value for both images, at 23,489 versus 23,467 gas.

## Proof binding

`Proofs/Cycle/NormalizeExecution.lean` proves the modified exact instruction
sequence with no additional hypotheses. `NormalizeMeaning.lean` and
`NormalizeBinding.lean` connect it to the unchanged word-subtraction meaning.
`Proofs/Cycle/Artifact.lean` assembles the 9,189 instructions to the exact
literal in `Proofs/Cycle/Bytes.lean`. Existing cycle/caller/global correctness
then feeds `Solution.lean` and the protected benchmark artifact. The allowed
axiom set remains `propext`, `Classical.choice`, `Quot.sound`.

Run `BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh modexp` for the documented local
Comparator and gas gate. Local execution uses the documented fake sandbox and
is not a ranked verification. The full gate result is recorded in the attached
research report; this README is not itself an acceptance receipt.

Decoded byte SHA-256:
`4a43d5e6471264bf96ca8df6229ba175c9539ef16920697b32171bd63a789d5e`.

## Attribution

This refinement builds directly on aerugo-ef v15 (GPT-6 Astra / Codex), the
retained v14 lineage, fkiene's compatible public refinements, and Th0rgal's
Gemini 3.1 Pro / Antigravity schedules. Claude's original contribution and all
inherited provenance and Apache 2.0 notices are preserved below and in the
provenance files. This iteration adds only the normalizer dead-code elimination
and exact proof/artifact integration. See `dependencies.json`.

---

## Inherited v15 documentation

# MODEXP: retain radix-240 values across repeated operations

This v15 candidate uses 374,487 gas on the 44 public seed-zero vectors,
versus 392,554 for fkiene's `de134b66-a42c-4b03-a575-3f9318a88ad8` on the same
inputs: 18,067 gas saved (4.60%). The executable is 11,164 bytes.

The eight-word route retains nine radix-240 digits across repeated Montgomery
squares and the terminal product. Joint operand lifetimes, instruction
scheduling, memory reuse and finalization reduce repeated conversion and
storage work. The four-word setup also specializes its known buffer pointer.

## Verification

`Solution.lean` connects the exact protected literal rendered from
`bytecode.hex` to `CycleSubmission.Global.correct`. The theorem covers every
valid padded MODEXP input, including the general fallback, given sufficient
gas. The proof uses only `propext`, `Classical.choice` and `Quot.sound`.

The main proof layers are:

- `Proofs/Cycle/Core.lean`: repeated arithmetic, normalization and output.
- `Proofs/CycleCaller/Spec.lean`: eight-word caller and operand encodings.
- `Proofs/CycleGlobal/Correct.lean`: dispatch, conversion, both widths and fallback.

From the challenge root, run `./setup.sh modexp`, then `./benchmark.sh modexp`.
The documented local mode is `BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh modexp`.

Decoded executable SHA-256:
`b158452c8397c428e5a13c0757c453b0462345ce11005604d9e3dee899f7b4e8`.

## Attribution and license

Claude found the original optimization in aerugo-ef's repository. This work
builds on aerugo-ef v14 and fkiene's compatible public refinements. Th0rgal's
Gemini 3.1 Pro / Antigravity schedules and other inherited implementations are
credited in the retained provenance. The new cycle, scheduling and proof
integration were developed with GPT-6 Astra / Codex.

`dependencies.json` declares direct dependencies. `INHERITED_PROVENANCE.json`
and `Provenance/` preserve the v14 declarations, attribution and historical
documents; their measurements and implementation descriptions refer to those
earlier versions. Original local work uses Apache 2.0; see `LICENSE` and the
upstream notices retained in the source.
