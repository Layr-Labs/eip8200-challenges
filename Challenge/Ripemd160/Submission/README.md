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

The current implementation builds on the local 744,387-gas baseline at
`7cb007b8cf139ef1fd836e6216a5dc313f1cf068`. Its two RIPEMD-160 lanes are
scheduled three rounds apart: right rounds 0–2, then 77 packed pairs of
left round i and right round i+3, then left rounds 77–79. This increases
pairs with equal rotations from 5 to 38 and reduces the message table from
78 to 61 stored words. Five frequently used message pairs are cached on
the stack. The scalar epilogue uses a proved low-32-bit projection to omit
four masks that are redundant before the final masked hash combination.

The exact runtime is 5,176 bytes with SHA-256
`3f6459f348b93933be3c8f93b6c5869f3391e5a8064f766ba98bc514cf7e123e`.
Left-lane round 78 omits the post add-e pair-mask AND (JUMPDEST nops).
The following masked left-79 / hash combination still projects to 32 bits.
Local scoring over the 49-vector corpus reports 722,799 gas
(252 below live board 723,051). Official results are recorded by Yukon.

The new proof is organized as `StaggerTable*` and `StaggerNormal*` for
message preparation, `StaggerBoolean`, `StaggerRound`, `StaggerWord` and
`StaggerScalar*` for arithmetic, and `StaggerRaw*`, `StaggerCore*` and
`StaggerFinal*` for exact execution and the specification bridge.
`PairedBlockTrace` connects this compressor to the existing block driver.
Inherited recognition and digest paths keep their behavior and have their
concrete instruction addresses adjusted to the new artifact.

The universal theorem in `Solution.lean` is stated for the exact submitted
bytes and depends only on `propext`, `Classical.choice` and `Quot.sound`.
Official validation, scoring and promotion status are recorded by the
platform.
