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

## Current candidate: unaligned table windows and hAt

The current candidate also uses the table-window idea from submission
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
against the original baseline. The current closed gas formula is
`3698 + 123852 * B + 3 * C + memCost(65 + 2 * B)`, where
`B = (inputSize + 72) / 64` and `C = (inputSize + 31) / 32`.
The full exact-bytecode Comparator remains the acceptance condition.

## Current candidate: zero-slot elimination and shorter loop increments

This candidate removes the compiler's zero result slot from the five hot
helpers that already consumed their other arguments in place (`xAt`,
`tableAt`, and `rotl`, called 1, 2, and 2 times per round). Each call site
replaces its `PUSH0` with a `JUMPDEST` and decrements the `DUP` depths that
reached past the slot; each helper body drops its consuming `ADD` and gains
one unreachable trailing `STOP`. Every edited region keeps its byte length,
instruction count, entry address, and all downstream program counters, and
every post-call stack is identical to before, so downstream `DUP` depths are
unchanged. The Boolean-function dispatch path is untouched.

The two 80-iteration line loops additionally replace
`POP; PUSH1 1; DUP2; ADD; SWAP1; POP; PUSH2; JUMP` with
`POP; PUSH1 1; ADD; PUSH2; JUMP` plus three unreachable `STOP`s, saving the
duplicated counter copy and its cleanup.

Per round this saves 4 gas in `xAt` (body plus call prologue), 8 in the two
`tableAt` calls, 8 in the two `rotl` calls, and 8 in the line-loop
increment: 28 gas per round, 4,480 gas per padded block, or 295,680 across
the 66-block public suite. The native
suite passes all 17 clean and dirty vectors at 7,945,631 gas. The closed gas
formula is `3698 + 119372 * B + 3 * C + memCost(65 + 2 * B)` with `B` and `C`
as above. The full exact-bytecode Comparator remains the acceptance
condition.
