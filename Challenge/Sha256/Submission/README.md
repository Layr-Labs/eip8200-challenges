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

The compression round now loads state word `h6` directly from memory at its
only hot call site instead of entering and returning through the shared `hAt`
accessor. An unreachable `PUSH3 0; POP` pad keeps the following `JUMPDEST` and
all downstream program counters fixed. This saves 39 gas per round, 2,496 gas
per padded block, and 162,240 gas over the public suite.

The adjacent fixed state-word `h5` load now uses the same direct-memory
specialization. Its length-preserving pad retains the next call boundary and
again saves 39 gas per round, 2,496 gas per padded block, and 162,240 gas over
the public suite.

The fixed `h7` load later in T1 is specialized identically, eliminating a third
hot `hAt` call while keeping its following arithmetic at the same PC. This
saves a further 39 gas per round and 162,240 gas over the suite.

The remaining seven fixed-index state loads in T2 and the working-state update
sequence are now specialized in one length-preserving batch. The two T2 loads
read `h2` and `h1` directly. The update sequence directly reads `h6`, `h5`,
`h3`, `h2`, and `h1` before their corresponding stores. Each site replaces the
generic `hAt` call and return with `PUSH2 address; MLOAD`, followed by unreachable
`JUMPDEST; PUSH3 0; POP` padding that preserves the next real instruction and
every later program counter. Each direct load saves 39 gas per round. Together
the seven sites save 273 gas per round, 17,472 gas per padded block, and
1,135,680 gas over the public suite.

The compression round's variable-index message-schedule load now computes the
`W[j]` address in place instead of calling the generic `wAt` accessor. The
nine-byte call sequence is replaced by `DUP3; PUSH1 5; SHL; PUSH2 800; ADD;
MLOAD`. This adds one structural instruction, so the unreachable pad after the
direct `h7` load is compacted from `JUMPDEST; PUSH3 0; POP` to `PUSH4 0; POP`;
bytecode length and the 810-instruction artifact are both unchanged. The
direct load saves 33 gas per round and the padding compaction saves one more,
for 2,176 gas per padded block and 141,440 gas over the public suite.

The adjacent variable-index `K[j]` lookup is now inlined as an overlapping
memory load. Instead of calling `kAt`, the round computes `4 + 4*j`, loads the
32-byte word beginning there, and applies the already-live 32-bit mask. The
last four bytes of that word are exactly the big-endian constant at
`32 + 4*j`, so the masked result is identical to the old
`MLOAD(32 + 4*j); SHR 224` path. Widening the following `PUSH2` instructions
to `PUSH3` absorbs the two extra structural instructions without changing any
later PC, the 1,524-byte length, or the 810-instruction artifact. This saves
36 gas per round, 2,304 gas per padded block, and 149,760 gas over the suite.

The five remaining working-state moves now fuse each already-specialized
fixed-address load with its corresponding store. Four shifts copy `h6` to
`h7`, `h5` to `h6`, `h2` to `h3`, and `h1` to `h2`; the fifth computes and
stores masked `h4 := h3 + t1`. Each direct `MLOAD`/`MSTORE` path replaces the
old accessor-return scaffolding while widened `PUSH5` addresses and unreachable
`JUMPDEST` padding preserve the local span, all downstream PCs, the 1,524-byte
length, and all 810 structural instructions. Every fused site saves 36 gas per
round, for 11,520 gas per padded block and 748,800 gas over the suite.

The shared `BSIG0` and `BSIG1` helpers now compute all three rotations from a
single duplicated 32-bit lane. For `BSIG0`, the code forms
`d := (x << 32) | x`, derives `d >> 2`, then shifts that result by 11 and 9
more bits to obtain the 13- and 22-bit rotations before XORing and masking.
`BSIG1` uses the analogous 6, 5, and 14-bit chain for rotations 6, 11, and 25.
Each caller also drops the obsolete output placeholder. Unreachable `PUSH1 0`
and `STOP` padding preserves both 44-byte helper spans, both caller spans,
every downstream PC, the 1,524-byte length, and all 810 instructions. Each
fused helper plus caller saves 180 gas per round; together they save 23,040
gas per padded block and 1,497,600 gas over the suite.

The four recurrence reads of `W[j-16]`, `W[j-15]`, `W[j-7]`, and `W[j-2]`
now compute their memory addresses directly from the live loop index. Adjusted
bases 288, 320, 576, and 736 make each address `base + (j << 5)`, exactly the
same slot as `(j-k) * 32 + 800`. Widened `PUSH4` constants and an executed
`JUMPDEST` preserve every local byte and instruction boundary. Each direct
load replaces a setup plus the generic `wAt` helper, saving 38 gas; the batch
saves 152 gas per recurrence iteration, 7,296 gas per padded block, and
474,240 gas over the suite.

The shared `SSIG0` and `SSIG1` helpers now compute both rotations from one
duplicated 32-bit lane. `SSIG0` derives rotations 7 and 18 with successive
right shifts of 7 and 11 bits, while `SSIG1` derives rotations 17 and 19 with
successive shifts of 17 and 2 bits. The helpers return the raw XOR values and
defer the 32-bit reduction to the recurrence's existing final mask. The two
direct `W` loads are fused with their helper jumps, and unreachable `STOP`
padding preserves every byte PC, the 1,524-byte length, and all 810 structural
instructions. The proof establishes low-32 congruence for both raw helpers and
lifts it through the recurrence additions. Together the two fused groups save
246 gas per recurrence, 11,808 gas per padded block, and 767,520 gas over the
suite.

The recurrence tail now writes `W[j]` directly instead of calling the generic
`wSet` helper. It reuses the live loop index to form `(j + 25) << 5`, which is
exactly `800 + 32*j`, performs `MSTORE`, discards the obsolete carried return
PC, and increments the loop counter in the same 20-byte, 15-instruction span.
This saves 22 gas per recurrence, 1,056 gas per padded block, and 68,640 gas
over the suite without moving any downstream PC or structural index.

The initial 16-word schedule loop now fuses each direct `MSTORE` with its loop
increment and back-edge. A single `DUP2` preserves the index across the store;
the old cleanup pair and separate increment scaffolding disappear into dead
`STOP` padding, preserving the 23-byte span and all 810 instruction indices.
This saves 13 gas per iteration, 208 gas per padded block, and 13,520 gas over
the suite.

The eight-word feed-forward loop now reuses one computed `32*i` offset for
both the saved-state and working-state loads, adds and masks the words, and
stores the result directly. This replaces both generic accessor calls and
their return scaffolding in the same 35-byte, 20-instruction span, preserving
every downstream PC and artifact index. It saves 65 gas per iteration, 520
gas per padded block, and 33,800 gas over the suite.

The BSIG0 helper is specialized for its only compression-round caller: it now
adds `Maj(a,b,c)`, applies the 32-bit mask, and jumps directly to the existing
post-T2 boundary. The caller drops its placeholder and return scaffolding;
one restored fall-through `JUMPDEST` keeps the artifact at 810 instructions.
This saves 9 gas per round, 576 gas per padded block, and 37,440 gas over the
suite.

Fresh local scoring of the exact submission bytes is 3,753,967 versus the
10,179,119 reference, a combined reduction of 6,425,152 gas. All 19 vectors
passed from both clean and dirty initial states with identical gas. The empty
vector costs 59,011 gas.

`Solution.lean` imports a candidate-specific raw-EVM proof under this editable
directory. Its entry trace executes the direct `PUSH2 0x03e5; JUMP`; the
candidate-specific compression trace executes the optimized increment; the
helper traces execute the new `Ch` and `Maj` schedules; and the downstream
proof establishes the SHA-256 specification for every calldata value. The
accompanying exact-gas proof accounts for a fixed cost of 1,499 gas and 57,220
gas per padded block, plus calldata copying and memory expansion.
