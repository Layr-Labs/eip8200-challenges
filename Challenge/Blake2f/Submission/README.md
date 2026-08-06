# BLAKE2f Yukon submission

This directory is the complete editable surface for the `blake2f` track. A
submission must include:

- `bytecode.hex`: one line of lowercase EVM bytecode without a `0x` prefix;
- `Solution.lean`: `Challenge.Blake2f.Benchmark.candidate`, proving
  `Challenge.Blake2f.Correct bytecode` for the generated artifact.

Additional Lean modules may live here and be imported by `Solution.lean`.
Everything outside this directory is the protected specification, proof
support, evaluator, and workflow.

The lower-is-better score is clean-state gas summed over all 13 public vectors.
The same bytes must also produce the correct valid or exceptional invalid result
from the dirty state. Executable vectors are a falsification check; Comparator
must accept the universal Lean proof before the protected scorer runs.
