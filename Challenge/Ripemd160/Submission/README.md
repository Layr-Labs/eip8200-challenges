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

## Prior candidate: direct stack-resident rounds (H10)

H10 retains the message schedule and replaces the compressor with two fully
unrolled 80-round lanes. Five working words stay on the EVM stack through each
lane. The right lane runs above the saved left result. Round templates use
immediate message-slot addresses, constants, and rotations, with inline Boolean
operations and 32-bit rotation. The three old working-state memory copies and
the round helper calls are no longer on the active compression path.

The exact artifact is 12,906 bytes. Native tests report 1,743,479 gas over all
17 clean vectors. All 17 dirty vectors also pass with the same gas total.
The measured formula is `3698 + 25400 * B + 3 * C + memCost(65 + 2 * B)`.
It is not a separate proved gas schedule. H09, the prior immediate-wrapper
candidate, passed local Comparator at 6,181,847 gas and 5,133 bytes.

The proof uses 42 instruction-aligned assembly chunks, five generic round
traces, and exact indexed certificates for all 160 sites. The scheduled words
match the pinned RIPEMD-160 message schedule. Both complete lane traces use
actual machine states with unchanged memory and active-word count. The final
61-instruction tail stores the five combined hash words in the exact program
order. `StackCorrect` connects these components to the outer block model and
the unchanged public Correct contract. `Solution.lean` is the benchmark entry.

Only the protected Comparator and scorer determine benchmark acceptance.
The final theorem must pass that check for the exact submitted bytecode.

## Prior candidate: compact shared stack rounds (H12)

H12 retains the stack-resident working words, schedule, and final combination.
It replaces H10's inline round bodies with 160 six-instruction wrappers and
ten shared helpers. Each wrapper supplies a return PC, rotation, message-slot
address, and helper PC. Each helper embeds its group constant. Both the helper
return JUMP and the wrapper's return JUMPDEST are executed and proved.

The exact artifact is 4,796 bytes and 2,583 instructions. The native suite
reports 2,292,599 gas over all 17 clean vectors. All 17 dirty vectors pass with
the same individual gas results. The measured formula is
`3698 + 33720 * B + 3 * C + memCost(65 + 2 * B)`.
This is a native measurement, not a separate proved gas schedule.

H09 was promoted at 6,181,847 gas. H10 failed before proof replay because the
protected generated-byte module exceeded its recursion limit. H12's smaller
byte array passes that isolated generator check without a harness change.

The proof uses 13 instruction-aligned assembly chunks, five generic helper
traces, exact call/helper/return locations, bounded 80-round lane composition,
and the final storage tail with its nonempty helper suffix. StackCorrect and
Solution retain the exact universal Correct contract. Acceptance still
requires the full protected Comparator and scorer.

## Prior candidate: compact rotation and return sequence (H14)

H14 keeps H12's shared helper design and changes only the common stack
permutations. It consumes the C input directly during its ten-bit rotation.
It also consumes the sum and rotation inputs directly when it computes T.
All masks, arithmetic, memory accesses, and call/return steps remain.

The artifact is 4,726 bytes and 2,513 instructions. The native suite reports
2,113,079 gas for all 17 clean vectors. All 17 dirty vectors pass with equal
paired gas. This saves 179,520 per frame suite, or 2,720 per compression block,
against H12. The measured formula is
`3698 + 31000 * B + 3 * C + memCost(65 + 2 * B)`.
It is not a separate proved gas schedule.

The five before-JUMP templates have lengths 44, 48, 49, 48, and 49.
The wrappers and final storage tail keep their previous positions. Each
helper has seven fewer instructions and bytes. All ten helper addresses,
160 wrapper targets, and the tail's 486-instruction suffix are updated.
The unchanged public Correct contract and protected Comparator remain the
acceptance conditions for these exact bytes.

## H16: merged permutations and deferred Boolean masks

H16 includes H15's merged T/C permutation, which removes two SWAPs per
helper. It also removes the early Boolean-result mask from groups 2 and 4.
The later sum mask, T mask, and C mask remain. The ordinary-kernel identity
`mask32 (K + (A + (X + F))) = mask32 (K + (A + (X + mask32 F)))`
justifies the change for all UInt256 inputs, including arithmetic wrap.
The equality applies after the sum mask; unmasked sums need not be equal.

The native suite reports 2,024,375 gas for each frame. All 17 clean and 17
dirty vectors pass with equal paired gas. The artifact is 4,682 bytes and
2,485 instructions. H16 saves 25,344 gas against H15, or 384 per block.
The measured formula is
`3698 + 29656 * B + 3 * C + memCost(65 + 2 * B)`.
This is not a separate proved gas schedule.

The five before-JUMP template lengths are 42, 46, 45, 46, and 45. All ten
helper PCs, 160 wrapper targets, and the tail's 458-instruction suffix match
the new artifact. The public Correct contract is unchanged. Protected
Comparator acceptance is still required for the exact submitted bytes.

## Prior candidate: reordered helper parameters (H18)

H18 pushes the rotation before the return PC. The helper entry is
`[xAddress, returnPC, rotation, A, B, C, D, E] ++ rest`.
After the sum mask, `SWAP3; POP; SWAP2` reaches the same state that H16
reached with one more `SWAP1`. All later operations and masks stay fixed.
The change applies to all ten helpers and all 160 wrappers.

The native suite reports 1,992,695 gas per frame suite. All 17 clean and
17 dirty vectors pass with equal paired gas. The artifact has 4,672 bytes
and 2,475 instructions. The saving against H16 is 480 per compression
block, or 31,680 per suite. The measured formula is
`3698 + 29176 * B + 3 * C + memCost(65 + 2 * B)`.
This is not a separate proved gas schedule.

The five before-JUMP lengths are 41, 45, 44, 45, and 44 instructions.
Wrapper lengths stay at 13 bytes and six instructions. The second PUSH
starts at wrapper PC + 2; the return stays at PC + 12. The tail has a
448-instruction suffix. The universal Correct contract is unchanged.

## Prior candidate: consume A in the shared sum (H20)

H20 consumes A instead of copying it and later discarding it. After the
Boolean and X addition, the stack is `[s, ret, r, A, B, C, D, E] ++ rest`.
`SWAP1; SWAP3; ADD` gives `[A+s, r, ret, B, C, D, E] ++ rest`.
The unchanged group constant and sum mask then produce H18's exact
pre-rotation stack. All later T/C operations, three masks, memory accesses,
and return semantics stay fixed. Full-width working inputs remain valid.

Each helper is two bytes and two instructions shorter and costs five less
gas. The exact artifact has 4,652 bytes and 2,455 instructions; the helper
block has 610 bytes. The five before-JUMP lengths are 39, 43, 42, 43, and 42.
All 160 wrapper targets are correct; 144 changed. Their lengths and return PCs are fixed.
The final tail has a 428-instruction suffix.

The native suite reports 1,939,895 gas, with all 17 clean and 17 dirty cases
correct and equal paired gas. The reduction from H18 is 800 per block or
52,800 per suite. The measured formula is
`3698 + 28376 * B + 3 * C + memCost(65 + 2 * B)`.
This is measured gas, not a separate proved gas schedule. The universal
Correct contract and protected acceptance checks are unchanged.

## Current candidate: consume A with the packed schedule (H21)

H21 combines the H20 round helpers with the same 528-byte ascending packed
schedule used in H19. The schedule PUSH2 at PC `0x72b` now targets `0x122c`.
Only its two immediate bytes change in the 4,652-byte H20 prefix. The new
helper starts at instruction 2455. Its final JUMP is instruction 2614 at
PC `0x143b`. The full candidate has 5,180 bytes and 2,615 instructions.
The unchanged final combination tail has a 588-instruction suffix.

The helper reads +60 decimal, +0, and +32 before all 16 ascending X stores.
Two byte-swap stages per input word produce the little-endian values.
The warm-up preserves the old active-word count. Separate raw, byte-order,
full-memory, active-word, state, and located-step proofs connect the helper
to the old scheduled-state model. The frame uses CalldataFits and a valid
block index, with one return JUMPDEST. The public Correct contract is fixed.

Native tests report 1,730,279 gas with all 17 clean and 17 dirty cases
correct and equal paired gas. This saves 209,616 gas from H20 and 52,800
from H19 per suite. Native gas is not an official server score.
