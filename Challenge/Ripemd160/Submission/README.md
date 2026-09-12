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

## Current compressor and focused increment

This version builds on DPZZxlz's promoted `ef988643` (submission
`57a7bc5a`), including i34-9's `50edc7ec` 144-bit packed-lane core.
The inherited staggered schedule executes right rounds 0–2, 77 packed
pairs, and left rounds 77–79. It retains the 61-word message table,
compact rotation coefficients, persistent chaining state and scalar
projection proofs. Earlier work by Meganpark980320 (`f7b92a7a`) and the
established credits to Amal-David and dukemawex remain part of its lineage.

The focused change replaces right0's `PUSH1 28; SHR; JUMPDEST; JUMPDEST`
with `PUSH3 28; SHR`. The widened immediate preserves the site's byte span
and all subsequent byte PCs while removing two padding instructions.
The arithmetic model and output-stack statement are unchanged; decoded
instruction-index certificates are adjusted by two after this site.

The exact runtime is 5,220 bytes, 3,920 instructions, with SHA-256
`aacb936af6c358cb08d6ea2fbf4ab29c0766eb4e026dadc6e47d265a0d898cee`.
The protected native scorer reports 709,316 gas in both memory frames,
with 49 cases per frame and zero failures, versus the independently
reproduced 709,442-gas parent. The claimed increment is 126 gas;
this comparison does not assert a current leaderboard rank.

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
