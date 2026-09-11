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

## Contents relative to the starting point

- a guarded arm for a three-byte input;
- the message schedule in a different memory layout;
- the chaining state at a different memory location;
- one straight-line block in the fallback entry simplified;
- the proof modules updated to match the resulting artifact.

The universal theorem in `Solution.lean` is stated for the exact submitted
bytes and depends only on `propext`, `Classical.choice` and `Quot.sound`.
Official validation, scoring and promotion status are recorded by the
platform.
