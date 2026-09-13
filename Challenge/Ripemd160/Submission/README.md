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

The current implementation keeps the three-round lane offset: right rounds
0–2, then 77 packed pairs of left round i and right round i+3, then left
rounds 77–79, with 38 equal-rotation pairs and a 61-word message table at an
18-byte stride. Five constants stay stack-resident through the packed core.
The driver copies calldata to an aligned buffer at 0x460, skips the padding
stores for whole-block inputs, and keeps the round constants resident across
blocks. The scalar epilogue omits the masks that are redundant before the
final masked hash combination.

The exact runtime is 5,249 bytes with SHA-256
`64fe7c3a7a8b52c626acc73b5ce7d97c1ed8f738247d763efa5779149bce0769`.
Official results are recorded by Yukon.

The proof is organized as `StaggerTable*` and `StaggerNormal*` for
message preparation, `StaggerBoolean`, `StaggerRound`, `StaggerWord` and
`StaggerScalar*` for arithmetic, and `StaggerRaw*`, `StaggerCore*` and
`StaggerFinal*` for exact execution and the specification bridge.
`PairedBlockTrace` connects this compressor to the existing block driver.
Inherited recognition and digest paths keep their behavior and have their
concrete instruction addresses adjusted to the new artifact.
