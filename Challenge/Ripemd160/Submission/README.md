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

## Earlier direct-entry candidate

The initial `PUSH2; JUMP` now targets the existing main-body `JUMPDEST` at
`0x03ee` directly. This skips twelve compiler-generated
`JUMPDEST; PUSH2; JUMP` forwarding stubs while preserving the 1,671-byte code
length and every downstream program counter. The expected saving is 144 gas
per invocation, or 2,448 gas across the 17-vector score suite.

The candidate-specific proof under this directory changes the structural
artifact and entry execution trace to the direct jump. The downstream
RIPEMD-160 functional proof is unchanged, and its exact-gas bridge accounts
for the reduced entry cost.

## Stack-consuming helper candidate

This candidate starts from promoted submission
`943c3303-c540-44c3-8049-73aee90390f3`. It keeps that submission's Boolean
jump table and the direct entry jump. It consumes helper arguments directly
and uses the caller's zero result slot to remove stack cleanup work.

| Helper | Previous base gas | New base gas |
| --- | ---: | ---: |
| xAt | 37 | 30 |
| wordSet | 42 | 36 |
| xSet | 40 | 36 |
| tableAt | 57 | 48 |
| rotl | 54 | 45 |

Memory expansion is unchanged. The changes save 7,904 gas per padded block,
or 521,664 across the 66-block public suite. The native scorer reports
8,685,426 gas with all 17 clean and dirty vectors correct. The exact-bytecode
Lean proof is the acceptance condition, not the executable vectors alone.

Bytecode size remains 1,830 bytes. Each edited helper keeps its original
entry address, allocated byte length, and instruction count. Unreachable
STOP instructions after each return JUMP preserve later addresses and
instruction indexes. All caller-visible helper contracts remain unchanged.

## Prior candidate: unaligned table windows and hAt

That candidate added the table-window idea from submission
`80dacb5` by `ercumentyildirim`. The logical table bases remain unchanged.
Four calls push `base - 31`. The helper loads a word at `base - 31 + i`
and selects byte 31. It consumes its arguments and the zero result slot.
This reduces tableAt from 48 to 27 gas. The same argument-consumption
change reduces hAt from 37 to 30 gas.

The byte correspondence proof requires `31 ≤ base` and `i < 80`.
All four actual table bases meet that condition. Separate memory bounds
prove that the unaligned loads do not increase the memory high-water mark.
The public correctness theorem and its calldata domain are unchanged.

The native suite passes all 17 clean and dirty vectors at 8,241,311 gas.
The saving is 444,115 against the prior helper candidate and 1,618,387
against the original baseline. Its closed gas formula is
`3698 + 123852 * B + 3 * C + memCost(65 + 2 * B)`, where
`B = (inputSize + 72) / 64` and `C = (inputSize + 31) / 32`.
The full exact-bytecode Comparator remains the acceptance condition.

## Prior candidate: stack-consuming Boolean helpers

This candidate also consumes the Boolean case index and helper arguments.
Two selection arms use bitwise XOR identities proved for all UInt256
inputs. The per-bit proof uses only the permitted axiom set; the earlier
bv_decide probe is not part of this source.

Boolean case costs are [42,51,54,54,54]. The native score is 8,027,999,
with all seventeen clean and dirty cases passing. The formula is
`3698 + 120620 * B + 3 * C + memCost(65 + 2 * B)`.
The generic Boolean trace and complete execution/gas proof build have
passed. The independent exact-bytecode Comparator remains the acceptance
condition. Run all Yukon commands in the benchmark work directory printed
by the clone command.

## Current candidate: immediate round calls (H09)

This candidate starts from the accepted 8,027,999-gas H08 implementation.
It appends 160 fixed round-call wrappers and points the block driver to the
new compressor at 0x726. Each wrapper supplies the known Boolean case,
message-word index, rotation, constant, and working-memory base. The existing
round helper, message schedule, three memory copies, and final hash combination
remain in use. The fixed calls remove runtime round-loop and parameter-load
work. Bytecode size is 5,133 bytes.

The native suite reports 6,181,847 gas with all 17 clean and 17 dirty cases
correct and equal clean/dirty gas. This is 1,846,152 gas below H08. The measured
formula is `3698 + 92648 * B + 3 * C + memCost(65 + 2 * B)`, with B and C as
defined above. This formula is not a separate proved gas schedule.

`ImmediateCorrect.correct` proves the required universal `Correct` contract.
Its proof checks the exact instruction artifact, all 160 call sites, both lane
recurrences, the final right-round zero slot, and the actual block entry and
exit states. Table and K/KP values persist across blocks; current hash words
are not assumed to equal the initial hash. The output bridge uses the actual
finite execution cost as a sufficient gas witness. It does not require the
old implementation's closed gas formula. Comparator must independently check
this theorem for the same bytes before the benchmark result is accepted.
