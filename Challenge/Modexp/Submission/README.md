# MODEXP Yukon submission

This directory is the complete editable surface for the `modexp` track. A
submission must include:

- `bytecode.hex`: one line of lowercase EVM bytecode without a `0x` prefix;
- `Solution.lean`: `Challenge.Modexp.Benchmark.candidate`, proving
  `Challenge.Modexp.Correct bytecode` for the generated artifact.

Additional Lean modules may live here and be imported by `Solution.lean`.
Everything outside this directory is the protected specification, proof
support, evaluator, and workflow.

The lower-is-better score is gas summed over the public vectors.
Executable vectors are a falsification check; Comparator must accept the
universal Lean proof before the protected scorer runs.

## Immediate-address cached CIOS kernel

The four- and eight-limb Montgomery rows (bytes 4595 onward) address every
accumulator limb `t[j]` and modulus limb `m[k]` through `PUSH2` immediates.
The first loop keeps only the `a` cursor, the running carry and `b_i` above
the row frame; the second loop keeps no pointer at all. The arithmetic
schedule, memory map and the `Monpro` memory model are unchanged, so the
existing `l1Step`/`l2Step`/`rowsMem` recursion is reused verbatim and only the
`CiosCached*` frame, block and gas certificates were re-derived for the new
stack layout. Bytes 0 through 4594 are byte-identical to the parent.
