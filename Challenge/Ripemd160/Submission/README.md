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
`d726c429-6404-43a6-8e97-e47798108b35`, source commit
`0dc7d4a03c770fcbd1a5f57c4ecf883968566402`, at 708,238 gas.
It replaces the final round-76 `DUP2; AND` at byte PCs 4552–4553 with two
`JUMPDEST` instructions. The final packed-state invariant preserves both lane
projections of the unmasked `d` and `e` values. Instruction addresses and
artifact size remain unchanged. The expected and measured saving is
4 gas per generic compression block, or 252 gas over the scored suite.

The inherited staggered implementation was originally developed from
the local 744,387-gas baseline at
`7cb007b8cf139ef1fd836e6216a5dc313f1cf068`. Its two RIPEMD-160 lanes are
scheduled three rounds apart: right rounds 0–2, then 77 packed pairs of
left round i and right round i+3, then left rounds 77–79. This increases
pairs with equal rotations from 5 to 38 and reduces the message table from
78 to 61 stored words. Five frequently used message pairs are cached on
the stack. The scalar epilogue uses a proved low-32-bit projection to omit
four masks that are redundant before the final masked hash combination.

The exact runtime is 5,206 bytes with 3,909 decoded instructions and SHA-256
`6a306fe2ba72feede43d774f5c1c17e124df354ebb91c5e4e31e7b9ce33ec181`.
The native scorer reports 707,986 gas in both memory configurations, with
all 49 cases passing. Full universal-proof and comparator validation are
in progress; these executable results alone do not establish acceptance.
Official results are recorded by Yukon.

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
