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

## Carry cached on the stack

The four- and eight-limb Montgomery kernels keep the accumulator's top word
(`TN`, memory address 2080) in the former negative-32 frame slot. Each row
updates that slot, and the complete product or square materializes it before
conditional subtraction. Pointer decrement constructs negative 32 with
`PUSH1 31; NOT`. Setup and the real restart instructions reset the cached carry.
The other retained values are the inverse, low modulus word, modulus words at
96, 64 and 32, and the low accumulator address.

`TnCacheMemory`, `TnCacheRowModel`, and `TnCacheSquareModel` connect the cached
representation to the existing arithmetic memory model. `TnCandidate*` modules
bind those transitions to this exact bytecode. `CarryFullRowsFour/Eight` and
`SquareLoop` connect them to the complete exponentiation driver. The eight-limb
square preserves its final carry through subtraction until the next real reset;
it does not assume that carry is zero at the square exit.

The word path includes the shortened table construction and later exponent load
from the public word-window optimization. A zero modulus follows the common
word path. Its output remains zero, but some zero-modulus inputs consume more
gas than earlier implementations.

## Exact artifact and evidence

The runtime is 5309 bytes and 4076 instructions, SHA-256
`e874ac02b4ac816790a316dba4a79cb3607c667ad6fdd2b5dcc86cff2997152e`.
The complete `Solution` builds with only `propext`, `Classical.choice`, and
`Quot.sound` in the final theorem's axiom footprint. The unchanged protected
renderer also admits these bytes with its default settings.

The protected native scorer reports 490481 gas on the 44 default inputs.
Finite execution checks include 100 scoring corpora and a separate EVM suite
with 445 verified outputs. Another 119 inputs exhausted the same 30-million-gas
budget in all compared images; those are not counted as verified outputs.
These measurements do not claim gas improvement on every possible input or
guarantee an official score.

The integration builds on ercumentyildirim's retained-accumulator branch
`8b8c605`, i34-9's word-window branch `87529cf0`, and ercumentyildirim's word
proof updates in `e63acd82`. It retains the inherited R4 and other arithmetic
work credited in those public branches, including DPZZxlz's contributions.
