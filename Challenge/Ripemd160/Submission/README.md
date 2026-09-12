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

This contribution starts from promoted frontier
`b03f99164286b128ef1cb5624a5f630930335d3c`, at 723,618 gas and 5,180 bytes.
The existing three-round stagger, 61-slot message table, and block driver are
retained. Five redundant masks are removed from the terminal calculation:
two from the final paired update and three from extraction of the left A, D,
and E registers. B and C are still masked before the remaining scalar
rotations. A sixth repeated message pair, at address 230, is cached on stack.

The exact runtime is 5,168 bytes with SHA-256
`76ce2a415dfd99bc36e92ce4898717796e5f20ecbb469b8040b250e66c13e0e8`.
The trusted native scorer reports 721,665 gas in both memory configurations,
a saving of 1,953 gas on the same corpus: 1,890 from the masks and 63 from the
cache. Official validation, scoring, and promotion are recorded by Yukon.

`StaggerLastStep` proves that the unmasked terminal update has the same left
and right 32-bit projections as the existing masked update. The generalized
`StaggerCoreCorrect.epilogue_crypto` needs only B and C canonical on entry;
the other registers can retain irrelevant upper bits. `StaggerFinalMemory`
connects these projections to the five masked final hash words. All prefix
rounds retain their original masks and arithmetic proof.

`StaggerRaw*` and `StaggerCore*` describe the exact regenerated runtime,
including the sixth cache word and instruction relocations. `PairedBlockTrace`
connects the compressor to the existing driver and universal correctness
statement. Inherited recognition and digest paths retain their proved
behavior with updated concrete addresses.

The universal theorem in `Solution.lean` is stated for the exact submitted
bytes. Its permitted axioms remain `propext`, `Classical.choice`, and
`Quot.sound`.
