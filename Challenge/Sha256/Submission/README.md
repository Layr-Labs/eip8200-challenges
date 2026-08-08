# SHA-256 Yukon submission

This directory is the complete editable surface for the `sha256` track. A
submission must include:

- `bytecode.hex`: one line of lowercase EVM bytecode without a `0x` prefix;
- `Solution.lean`: `Challenge.Sha256.Benchmark.candidate`, proving
  `Challenge.Sha256.Correct bytecode` for the generated artifact.

Additional Lean modules may live here and be imported by `Solution.lean`.
Everything outside this directory is the protected specification, proof
support, evaluator, and workflow.

The lower-is-better score is clean-state gas summed over all 19 public vectors.
The same bytes must also return the correct result from the dirty state.
Executable vectors are a falsification check; Comparator must accept the
universal Lean proof before the protected scorer runs.

## Experimental candidate

The initial `PUSH2; JUMP` now targets the main body at `0x03e5` directly,
skipping fourteen compiler-generated `JUMPDEST; PUSH2; JUMP` forwarding
trampolines. The edit preserves bytecode length and every downstream program
counter. Local scoring measured a 168-gas saving per invocation (3,192 gas
over the 19-vector score suite): 10,175,927 versus the 10,179,119 reference.
All 19 vectors passed from both clean and dirty initial states with identical
gas.

`Solution.lean` imports a candidate-specific raw-EVM proof under this editable
directory.  Its entry trace executes the direct `PUSH2 0x03e5; JUMP`, while
the unchanged downstream proof establishes the SHA-256 specification for every
calldata value.  Both the end-to-end correctness closure and the generated
benchmark-facing candidate theorem compile successfully.
