# RIPEMD-160 Yukon submission

This directory is the complete editable surface for the `ripemd160` track:

- `bytecode.hex` — one line of lowercase EVM bytecode without a `0x` prefix;
- `Solution.lean` — `Challenge.Ripemd160.Benchmark.candidate`, proving
  `Challenge.Ripemd160.Correct bytecode` for the generated artifact;
- the Lean modules under `Proofs/` imported by `Solution.lean`.

## Provenance

This submission starts from promoted submission
`1151093f-45e9-4fb6-91f5-7120739684b4` and retains the public source lineage
of that submission and of every promotion it inherits from. Two recognition
and digest lemmas are taken from previously promoted submission
`cf170158-635a-4916-a3ca-220a0d3a4099` (co-authored by Amal-David). Source
authorship is not reassigned.

## Current compressor

The current parent is promoted `7a72a7e8`, submission
`b0cafa1f-5ffe-48f3-9a7c-b4cebcb75e91` by Meganpark980320. Its 144-bit-spaced lanes are
scheduled three rounds apart, with 77 paired rounds and a 61-slot message
table. The parent's late caches at addresses 342 and 252, terminal75/76
mask omissions, scalar projections, optimized final-addition/cleanup tail,
and earlier public contributions are retained.

This increment replaces the normal 16-bit endian-mask quotient with its
exact PUSH30 literal. Gas-neutral operand reorderings make the resulting
encoding fit the unchanged protected artifact compiler. This technique
builds on Meganpark980320's public operand-order notes; inherited core
work by i34-9 and the earlier contributor lineage remains attributed.

The runtime is 5,207 bytes, with SHA-256
`7759443cee0548a9e541a330c494c1b920383c0cc6e2d53abfb51c82546c8b7c`.
The protected native scorer reports 705,109 gas in both memory frames,
versus 705,529 for the independently reproduced parent: a 420-gas saving.
Full exact-artifact and secure benchmark validation must pass before submission.
Official acceptance, scoring and promotion are separate platform outcomes.

The new proof is organized as `StaggerTable*` and `StaggerNormal*` for
message preparation, `StaggerBoolean`, `StaggerRound`, `StaggerWord` and
`StaggerScalar*` for arithmetic, and `StaggerRaw*`, `StaggerCore*` and
`StaggerFinal*` for exact execution and the specification bridge.
`PairedBlockTrace` connects this compressor to the existing block driver.
Inherited recognition and digest paths keep their behavior and have their
concrete instruction addresses adjusted to the new artifact.

The universal theorem in `Solution.lean` is stated for the exact submitted
bytes. Validation permits only `propext`, `Classical.choice` and `Quot.sound`.
Official validation, scoring and promotion status are recorded by the
platform.
