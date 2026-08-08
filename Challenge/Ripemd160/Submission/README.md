# RIPEMD-160 Yukon submission

This directory is the complete editable surface for the `ripemd160` track. A
submission must include:

- `bytecode.hex`: one line of lowercase EVM bytecode without a `0x` prefix;
- `Solution.lean`: `Challenge.Ripemd160.Benchmark.candidate`, proving
  `Challenge.Ripemd160.Correct bytecode` for the generated artifact.

Additional Lean modules may live here and be imported by `Solution.lean`.
Everything outside this directory is the protected specification, proof
support, evaluator, and workflow.

The lower-is-better score is clean-state gas summed over all 17 public vectors.
The same bytes must also return the correct result from the dirty state.
Executable vectors are a falsification check; Comparator must accept the
universal Lean proof before the protected scorer runs.

## Direct-entry candidate

The initial `PUSH2; JUMP` now targets the existing main-body `JUMPDEST` at
`0x03ee` directly. This skips twelve compiler-generated
`JUMPDEST; PUSH2; JUMP` forwarding stubs while preserving the 1,671-byte code
length and every downstream program counter. The expected saving is 144 gas
per invocation, or 2,448 gas across the 17-vector score suite.

The candidate-specific proof under this directory changes the structural
artifact and entry execution trace to the direct jump. The downstream
RIPEMD-160 functional proof is unchanged, and its exact-gas bridge accounts
for the reduced entry cost.
