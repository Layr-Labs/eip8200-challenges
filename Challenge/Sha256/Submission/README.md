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

## Optimized candidate

The initial `PUSH2; JUMP` now targets the main body at `0x03e5` directly,
skipping fourteen compiler-generated `JUMPDEST; PUSH2; JUMP` forwarding
trampolines. The edit preserves bytecode length and every downstream program
counter. This saves 168 gas per invocation, or 3,192 gas over the public
19-vector suite.

The compression loop's six-byte round-counter increment at byte offset
`0x039d` is also rewritten from `PUSH1 1; DUP2; ADD; SWAP1; POP` to
`PUSH1 1; ADD; JUMPDEST; JUMPDEST; JUMPDEST`. The replacement is stack- and
length-preserving, reduces the increment cost from 14 to 9 gas, and executes
64 times per padded block. It saves 320 gas per block and 20,800 gas over the
suite's 65 padded blocks.

The shared `Maj` helper at byte offset `0x00e9` now evaluates the equivalent
Boolean identity `(x & y) | (z & (x | y))`. The new stack schedule uses nine
very-low-cost operations rather than eleven; two unreachable `STOP` bytes
preserve the following program counter. This saves 6 gas per helper call, 384
gas per padded block, and 24,960 gas over the suite.

The shared `Ch` helper at byte offset `0x00d4` now uses the equivalent identity
`z ^ (x & (y ^ z))`. Its stack schedule removes one executed very-low-cost
operation; one unreachable `STOP` byte preserves the following program
counter. This saves 3 gas per helper call, 192 gas per padded block, and 12,480
gas over the suite.

The same direct-add counter rewrite is now applied to the four remaining
compiler-generated increments at offsets `0x01a8`, `0x01e1`, `0x0251`, and
`0x03d7`. These are reached 8 times per call and 72 times per padded block in
aggregate. The four edits save another 24,160 gas over the public suite.

The shared rotate-right helper at byte offset `0x0004` now duplicates the
32-bit lane with `(x | (x << 32)) >> n` before masking, instead of computing
the left and right halves separately. This removes two executed very-low-cost
operations while two unreachable `STOP` bytes preserve all following program
counters. The helper is called 576 times per padded block, saving 3,456 gas per
block and 224,640 gas over the suite.

The five shared memory accessors at offsets `0x0101`, `0x0117`, `0x012b`,
`0x013e`, and `0x0152` now consume their index and value arguments directly.
The three loads avoid a redundant duplicate and cleanup pair, saving 5 gas per
call; the two stores avoid two duplicates and two cleanup pops, saving 10 gas
per call. Unreachable `STOP` padding keeps every later program counter fixed.
Across the concrete call graph this saves 8,600 gas per padded block and 40
gas per invocation, or 559,760 gas over the public suite.

Fresh local scoring of the exact submission bytes projects 9,309,127 versus
the 10,179,119 reference, a combined reduction of 869,992 gas. All 19 vectors
passed from both clean and dirty initial states with identical gas.

`Solution.lean` imports a candidate-specific raw-EVM proof under this editable
directory. Its entry trace executes the direct `PUSH2 0x03e5; JUMP`; the
candidate-specific compression trace executes the optimized increment; the
helper traces execute the new `Ch` and `Maj` schedules; and the downstream
proof establishes the SHA-256 specification for every calldata value. The
accompanying exact-gas proof accounts for a fixed cost of 1,499 gas and 142,684
gas per padded block, plus calldata copying and memory expansion.
