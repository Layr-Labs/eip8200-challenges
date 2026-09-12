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

The submission extends frontier `ef9886436c09a5666661faa43bc311b6b5b77bb9`,
which scores 709,442 gas. It preserves the inherited staggered schedule,
144-bit lane separation, compact rotations, persistent chaining state, and
61-word message table. The previously promoted padding improvement is restored; the newest parent had reverted it. This saves a further 288 gas, for 351 gas total against the current parent. Existing public source authorship is retained.

A fifth reusable stack value is introduced only after state packing, once
the last deep access to the chaining state has completed. It holds the
message pair at memory address 900. Three subsequent reads use DUP; the
extra value is removed in the existing tail cleanup. The exact change
saves one gas per compression, or 63 gas across the 49 benchmark inputs.
Both native memory configurations score 709,091 gas.

42 adjacent DUP pairs before commutative arithmetic operations
have their operand order exchanged. These transformations preserve the
stack result, instruction count, and gas. They reduce the literal size
seen by the default protected artifact compiler, which otherwise exceeds
its unchanged recursion limit on this candidate.

The exact runtime has 5,216 bytes and SHA-256
`2a398e96692d6c77b4587f655cfd7748637f5bd0a996439097368c198325f8be`.
The `.late` register is distinct from inherited `.cache 500`, which holds
the fifth chaining word. Raw bytecode templates and semantic stack shapes
are generated for the exact candidate. Existing arithmetic identities
justify the exchanged operands. The final cleanup removes `.late` before
the unchanged hash combination, and concrete code addresses are relocated.

The universal theorem in `Solution.lean` is stated for the exact submitted
bytes. Official validation, scoring, and promotion are recorded by Yukon.
