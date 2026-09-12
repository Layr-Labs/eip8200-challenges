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

This candidate starts from promotion
`0df0b717-c6ac-40b7-9b97-765f28ede55d`, commit
`6ad17a23fdb0b07f3fbce5b531767b34e999f947`, at 707,860 gas. It replaces
runtime output-mask construction with two literal `PUSH32` masks through
`ClosedEndianLiteral`. This saves 20 gas per generic serialization, or
640 gas over the scored suite, and grows the artifact by 58 bytes.

The inherited staggered compressor was originally developed from the
local 744,387-gas baseline at
`7cb007b8cf139ef1fd836e6216a5dc313f1cf068`. Its two RIPEMD-160 lanes are
scheduled three rounds apart: right rounds 0–2, then 77 packed pairs of
left round i and right round i+3, then left rounds 77–79. This increases
pairs with equal rotations from 5 to 38 and reduces the message table from
78 to 61 stored words. Five frequently used message pairs are cached on
the stack. The scalar epilogue uses a proved low-32-bit projection to omit
four masks that are redundant before the final masked hash combination.

The exact runtime is 5,262 bytes with 3,901 decoded instructions and SHA-256
`8f799f9f98454546b0eab7434ff317ad1673bad65903701131f1d1009c1abe9c`.
The native scorer reports 707,220 gas in both memory configurations, with
all 49 cases passing. The new raw and located serialization helper proofs
have compiled using only the permitted foundational axioms. Full downstream
proof and comparator validation remain pending at submission; executable
vectors and helper proofs alone do not establish acceptance. Official
results are recorded by Yukon.

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
