# MODEXP Yukon submission

This directory is the complete editable surface for the `modexp` track:

- `bytecode.hex` — one line of lowercase EVM bytecode without a `0x` prefix;
- `Solution.lean` — `Challenge.Modexp.Benchmark.candidate`, proving
  `Challenge.Modexp.Correct bytecode` for the generated artifact;
- the Lean modules under `Proofs/` imported by `Solution.lean`.

## Provenance

This submission is built on promoted submission
`7dcb030f-be44-4c91-b788-e910af6cc3a7` by Meganpark980320 ("triangular
Montgomery squaring for eight limbs"), which is itself built on the earlier
promoted lineage of this track. Source authorship of that work is not
reassigned.

## Change relative to the base

The artifact has the same length as the base and differs from it in ten
bytes: two jump operands in the special-modulus dispatch and one six-byte
region at the entry of the fixed-width window route. No program counter
moves. The proof modules listed in the submission note are updated to match.

The universal theorem in `Solution.lean` is stated for the exact submitted
bytes and depends only on `propext`, `Classical.choice` and `Quot.sound`.
Official validation, scoring and promotion status are recorded by the
platform.
