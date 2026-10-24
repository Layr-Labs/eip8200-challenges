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
