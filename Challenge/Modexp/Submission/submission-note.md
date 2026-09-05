# MODEXP: semantic zero-modulus-length exit in the existing pair pre-test

Model: GPT-6 Pro
Harness: ChatGPT

Effort: high

## Drafting status and validation boundary

This is a complete proof-source candidate, not a successful Lean-build log. During
preparation, the new Lean source was not elaborated, Comparator was not run, and the
protected scorer was not executed in the drafting environment. No server submission
was sent. The observed 2,282-gas result is from an independent interpreter.

The accompanying launcher appends an actual-local-validation section to a separate
public note only after the pinned source build and unmodified benchmark succeed.
Do not remove the distinction or treat the source zip alone as kernel acceptance.
All new theorem bodies are supplied without intentional gaps, but an elaboration,
API, or resource failure can still require repair before submission.

## Refreshed base and attribution

The exact base is `8d4880ab8e83bea56383282c062fa15ab8428a05` in
`Layr-Labs/eip8200-challenges`. This is newjordan's absolute-32-byte-alignment
MODEXP dispatcher with one-word pre-tests for both same-size guard pairs. Its
published protected result is 2,354 gas over 13/13 vectors, at 4,374 bytes and
1,811 instructions. The canonical hex-text SHA-256, including a final newline, is
`f8b20b904b72506ddfc67eecb469c7f4b0ec5f1ef30b99b0ec7ab75caf757ffe`.

The previous 2,527-gas crown was `51b82ef` / commit `68f07cc`. A 2,360-gas
candidate being prepared on that old source was overtaken by the new 2,354-gas
promotion. That obsolete bytecode and its proof overlay are not part of this package.
The new candidate is rebuilt and tested on the exact newly promoted artifact.

Credit for the reference body, modular arithmetic, bytecode execution machinery,
exact-calldata memoization and existing result certificates remains with the
repository contributors. The base note credits newjordan's preceding work and
terrapinelf's `0996ad1` reference lineage, including earlier contributions by
exakoss, brockelmore and others. Their unchanged proof modules and attribution are
retained. This patch is Apache-2.0 and does not claim authorship of the inherited
MODEXP algorithms or mathematical certificates.

## Objective and unchanged trust boundary

The goal is lower measured public-suite gas while retaining the exact statement
`Challenge.Modexp.Correct bytecode`. No trusted specification, valid-input predicate,
scorer, toolchain, dependency pin, comparator configuration, gas semantics or allowed
axiom policy changes. Edits are confined to `Challenge/Modexp/Submission`.

The implementation still contains the crown's exact-public-input memoization. Its
score is not presented as general acceleration of arbitrary RSA computations. The
new path itself is a general semantic case: a zero declared modulus byte length
requires an empty result for every valid tuple, regardless of the other operand
values. All nonselected calls follow existing guarded code and the reference.

## Existing control flow in residue bucket 20

The two 98-byte public inputs, zero exponent and zero modulus length, share residue
20 modulo 26. The unchanged byte-table dispatcher selects the V2 pre-test at PC
1536. In the crown, that pre-test loads calldata word 32, compares it to one, and
jumps to the full V3 guard at PC 1632 when equal. Otherwise it falls through to the
full V2 guard at PC 1547. This avoids scanning both full guards but still performs
unnecessary comparisons before the zero-modulus-length return.

The candidate changes the pre-test to load word 64, compare it to zero, and jump
directly to V3's existing empty-return block at PC 1698. When the word is nonzero,
the exact same fall-through to the V2 body remains. A valid input that fails the
complete V2 guard follows its original direct reference fallback.

The new pre-test is therefore:

```text
1536 JUMPDEST
1537 PUSH1 64
1539 CALLDATALOAD
1540 PUSH1 0
1542 EQ
1543 PUSH2 1698
1546 JUMPI
1547 ... existing complete V2 guard ...
```

The destination already contains the crown's certified return block:

```text
1698 JUMPDEST
1699 PUSH0
1700 PUSH0
1701 RETURN
```

PUSH1 zero is intentionally retained instead of replacing it by PUSH0: keeping the
width preserves every existing instruction boundary and index. This patch optimizes
the unnecessary full guard, not the encoding of that one constant.

## Why the direct return is universally sound

`MachineState.readWord input 64` reads the third EIP-198 length word. The existing
lemma `Challenge.EvmProof.Bytes.readWord_toNat` identifies its natural-number value
with `modulusSize input`. Equality with the zero UInt256 word therefore implies
`modulusSize input = 0`, with no approximation or unchecked numerical assumption.

The specification is defined with the branch `if msize = 0 then ByteArray.empty`.
Consequently the already-certified empty-return state has exactly the required
result for every input taking the new true branch. There is no need to compare the
base-length word, exponent-length word, or payload against a fixed test vector.
Those values cannot change the result under this semantic premise.

On a false pre-test, execution still enters the existing V2 body in precisely its
proved state: PC 1547, empty stack, untouched memory, and the same calldata and
initial machine fields. The full V2 guard either returns its certified result or
falls back to the reference. The proof does not need to infer the old exponent-word
condition from the new modulus-word condition, and does not assume that a residue
uniquely identifies the public input.

## Exact byte changes

Only three bytes differ from the 4,374-byte crown:

| Byte offset | Old | New | Role |
|---:|---:|---:|---|
| 1538 | 0x20 | 0x40 | Load modulus-length word instead of exponent-length word |
| 1541 | 0x01 | 0x00 | Compare against zero rather than one |
| 1545 | 0x60 | 0xa2 | Retarget PC 1632 to PC 1698 |

The instruction-list changes are exactly:

```text
1117: PUSH1 32   -> PUSH1 64
1119: PUSH1 1    -> PUSH1 0
1121: PUSH2 1632 -> PUSH2 1698
```

Every opcode and instruction boundary is unchanged. The number of bytes and
instructions remains 4,374 and 1,811. The table dispatcher, all full guard bodies,
all return blocks, and the complete reference body are untouched.

Candidate canonical hex-text SHA-256:
`932bbf1aafe450fdf1a9dc47c5664f38ac71fa4a2639c619693f1edf323ea760`.

Candidate raw-byte SHA-256:
`b700aada2909a42794b41c19a7a41fa0da9d8ca3f1a99b12990ba10c33c47f1e`.

## Complete proof-source patch

`Bytes.lean` changes only the three corresponding byte-array literals.
`Artifact.lean` changes the three exact PUSH operands while retaining the existing
assembly, well-formedness, program-counter and jump-destination machinery. The
new target is the existing JUMPDEST at instruction 1189. No new PC table is required.

`V2/Paths.lean`, the pre-test portion of `V2/Trace.lean`, and the two pre-test
compositions in `V2.lean` use the new offset, comparison value, and destination.
The proof shapes are inherited: symbolic prefix evaluation, equality/non-equality
reasoning for the EVM EQ condition, and the existing generic taken-JUMPI lemma.
The full guard's prelude, comparisons, arithmetic-result certificate, and fallback
trace are unchanged.

`SemanticZero.lean` supplies the general specification bridge and lifts the
existing `V3.Trace.run_return` to a GasSteps trace. The final state is the actual
existing state with PC 1701, empty stack and memory, zero active words, returned
halt status and empty output. No mismatched parent's stack state is asserted.

`Memo/Main.lean` supplies the unchanged generic absolute-alignment dispatcher trace
and a concrete destination witness for every residue. `Memo/Correct.lean` composes
those prefixes with complete leaf handlers, preserves the V9/V10 pre-test exactly,
and uses the semantic zero result in bucket 20. It covers full-guard hits, misses,
and the reference fallback for all valid input cases. The final impossible residue
case follows from `Nat.mod_lt`.

The selected final state and execution trace feed the existing
`GasSteps.toEventuallyEvaluates` bridge and then `correct_of_directProof`. The
original `Solution.lean` remains unchanged, including its exact theorem about the
independently generated protected byte array. No `sorry`, `admit`, new axiom,
`native_decide`, external oracle, proof-only answer, or weakened acceptance statement
is introduced in the authored source. These are source properties, not a claim
that an axiom audit has already run on this candidate.

## Measured independent-interpreter result

Before evaluating the patch, the interpreter reproduced every one of the newly
published crown's thirteen individual gas rows and checked the expected output
bytes. The new candidate changes only the zero-modulus-length row:

```text
zero modulus length: 145 -> 73 gas
all other twelve rows: unchanged
suite total: 2354 -> 2282 gas
saving: 72 gas, approximately 3.06 percent
```

These measurements are not relabeled as protected scorer results. Additional
falsification uses one-bit mutations, padded/extended/truncated inputs, random
bounded-header tuples, and targeted residue collisions. Valid returned outputs are
compared with an independent padded parser and Python modular exponentiation.
Misses are checked at PC 1196 for empty stack, untouched memory and zero active
words; the interpreter does not execute the complete reference. Invalid-domain
inputs are smoke tests, not exceptional-behavior equivalence evidence.

## Reproduction and gate

The supplied launcher first checks the public promoted source and refuses an
unfamiliar MODEXP/trust base. It invokes the unmodified pinned `setup.sh modexp`,
applies the synchronized patch, compiles the candidate closure one module per
process, and runs the unmodified benchmark. It rejects failures, mismatched
protected bytes, and a non-improving actual score. Only then does it create a
complete checked-local source archive and a separate note with actual results.

The default uses the repository's documented insecure-local mode. That still runs
proof replay and the scorer but is not ranked sandbox security or server acceptance.
The ranked-local option keeps the normal Linux requirements. The launcher never
calls Yukon submit automatically, and the user must check the production board
before sending the printed command from the same checkout.

## Limitations

This candidate was rebuilt against the refreshed GitHub accepted source. That read
does not independently establish the absence of newer production/pending results.
The drafting environment could not install and run the pinned Lean compiler, and
the hosted workflow route was unavailable. Therefore compilation, independent-kernel
replay, and protected gas measurement remain required local validation stages.
The supplied theorem bodies have no intentional gaps, but source completeness and
finite runtime testing are not substitutes for those checks. Failed validation
should preserve logs for repair, not submit the new hex with the old proof.
