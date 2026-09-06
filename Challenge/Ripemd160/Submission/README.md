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

## Prior candidate: consume A with the packed schedule (H21)

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

## Current candidate: bounded RotationFold with the packed schedule (H22c-packed)

H22c-packed is the current native candidate. It combines two bounded helper
folds with the unchanged 528-byte ascending packed schedule helper. The native
measurement is 5,150 bytes, 2,585 instructions, and 1,635,239 gas per frame.
The result is 95,040 gas lower than the H21 native measurement. Native gas is
not an official server score. The measured formula is
`3698 + 23760 * B + 3 * C + memCost(65 + 2 * B)`, where
`B = (inputSize + 72) / 64` and `C = (inputSize + 31) / 32`.

The C fold replaces:

```text
DUP1 PUSH1 10 SHL SWAP1 PUSH1 22 SHR OR PUSH4 0xffffffff AND
DUP1 PUSH1 32 SHL OR PUSH1 22 SHR PUSH4 0xffffffff AND
```

The C input remains a full-width UInt256 value until the preserved
`PUSH4 0xffffffff; AND`. The replacement uses bitwise OR. It does not use the
invalid multiplication shortcut `C * (2^32 + 1)` for arbitrary C.

The T fold replaces:

```text
DUP1 DUP3 SHL SWAP2 PUSH1 32 SUB SHR OR
DUP1 PUSH1 32 SHL OR SWAP1 SHR
```

The sum `q` is already masked to 32 bits. Every wrapper uses the complement
rotation payload `32-r` exactly once for this fold. The new stack prefix is
`[q, 32-r, ret, ...]`. The raw result is
`((q << 32) OR q) >> (32-r)`. At `r=0` the raw result is `q`; at `r=32` it is
`(q << 32) OR q`. The later addition and 32-bit mask preserve the required
round result at both endpoints.

All three 32-bit masks remain. All five groups, both constant tables, all
working-lane order, return behavior, suffix behavior, and the final
combination tail remain fixed. The 160 wrappers remain 13 bytes and six
instructions. Their return PC remains wrapper PC plus 12. The H22c prefix has
4,622 bytes and 2,425 instructions. The appended schedule helper starts at
PC `0x120e`, instruction index 2,425, and its final JUMP is at PC `0x141d`,
instruction index 2,584. The packed tail suffix is 558 instructions.

Native testing passed 12/12 tests. Main independently reran all twelve tests.
Each of the four trusted native scorer processes passed 34 rows: 17 clean and
17 dirty. All rows were correct, and every clean/dirty pair had equal gas.

The generic proof build passed 1,020 jobs, and the fresh seven-theorem
`H22RawAudit` passed with only the three allowed axioms. The exact Artifact
build, fresh Artifact audit, and independent source review also passed.
The complete `StackCorrect.correct` build passed 1,091 jobs. Fresh Correct,
Site, and Raw audits also passed with only the allowed axioms. The local
Comparator accepted H22. The server promoted its exact artifact at
1,635,239 gas. Each later candidate requires its own protected checks.

## H27: full-width paired rounds and the exact C-fold

H27 is the current locally verified candidate after H25. The native
measurement is from the trusted binary on macOS, not the ranked server.
The public files are `Challenge/Ripemd160/Submission/bytecode.hex`
and `Challenge/Ripemd160/Submission/Proofs/Bytecode/StackCorrect.lean`.

| candidate | status | gas | bytes | instructions |
| --- | --- | ---: | ---: | ---: |
| H24 `c6ac2fcc` | promoted | 1,429,319 | 5,020 | 2,593 |
| H25 `044d5a48` | promoted | 1,387,079 | 5,060 | 2,553 |
| H26 | dominated; not submitted | 1,323,719 | 4,940 | 2,513 |
| H27 | local native candidate | 1,281,479 | 4,980 | 2,473 |

H25 source SHA-1 is `576dbe880abd933fe853367e0434f42b99879410`. H27 saves
105,600 gas versus H25 and 147,840 versus H24, at 1,600 gas per 512-bit
block. H26 removed a mask; H27 also changes the C-fold.

The C-fold changes from `DUP1 PUSH1 32 SHL OR PUSH1 22 SHR` to
`PUSH5 0x100000001 MUL PUSH1 22 SHR`. The exact pure raw operation is
`((UInt256.ofNat 0x100000001).mul C).shiftRight (UInt256.ofNat 22)`.
The exact raw evaluator theorem preserves all five full-256-bit output words,
equal to two pure raw rounds, and preserves full memory. It proves ordered
`activeWords` for the two MLOADs; the production `activeWords ≥ 67` bound
makes the count unchanged.

The generic raw premises include a running state, `rest.length < 1012`,
`r0 ≤ 32`, `r1 ≤ 32`, f0 constant `0`, and the memory, stack, and suffix conditions.
Each helper executes two rounds; the lane composes 40 pair calls. The generic
rotation proof is universal for rotations at most 32. Only semantic
`WorkingRepresents` identifies canonical 32-bit B/C with `embeddedUInt32` and
uses low A/D/E; the generic raw theorem remains full width. The bound
`C < 2^32` is used only for that semantic bridge. At `C = 2^32 + 1`, MUL
gives low result 2,048 and the old OR gives 1,024.

The packed bytecode uses 64-byte chunks: 4,980 bytes require 78 chunks. The
nonpacked main uses 70 chunks. The exact Lean Artifact has 14 instruction
chunks: 12×200, 73, and empty. Its ASCII hex SHA-256 is
`3f9a9f23df70cf8ec172e2840caf20e86ea415047224fcd97b996e9152519a08`; its
decoded-byte SHA-256 is
`ec8d3612bcf4240063117b7176d36bcac57fd1f11be37d718a076b50cb1cb9c0`.

The trusted scorer has 34 rows: 17 clean and 17 dirty, all PASS with equal
clean/dirty gas. The 1,281,479 score is the total for the 17 clean rows. A
separate native test oracle ran 21,780 cases across H26 and H27 in seven tests:
2 variants × 10 helpers × 33 × 33 rotations. All seven tests passed. Empty
costs 22,307 gas; 1,000 bytes cost 298,503 gas.

Main reports proper `StackCorrect.correct` 1,087 PASS and fresh
`H27CorrectAudit` PASS with only the three allowed axioms. Negative proper
1,020 plus fresh 2, Lane fresh 5, Sites fresh 10, Endpoint/Seams proper 1,077,
and outer fresh 7 all PASS. The independent review and fresh 26-check full
audit also passed. Local H27 Comparator and server validation are pending.

The actual f0 change is q1 XOR/add grouping and C-fold MUL. Negative failures
were a missing fold-to-two-shift equality, f2 fixed by
`hsecondRotC'.trans hT1_sem.symm`, and an f4 broad `simp` hitting the
4-million heartbeat limit after 84 seconds. The final direct fix was
`raw_rotate_target.trans hT1_sem.symm`. Premises and limits did not change.

Reproduce from a public checkout with:

```text
./.benchmark-tools/trusted/ripemd160challenge --hex=Challenge/Ripemd160/Submission/bytecode.hex --csv
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
```

Root audits and generator logs are ignored and are not uploaded. H23 dense
packing and the H28 cache are research only; H28 had worse gas. Credit public
terrapinelf ScratchLow/StackCompression PR 69, commit
`6e97b9236cdf63c69e9e558828eee92ea3146ec9`, and ercumentyildirim for the
inherited compiler/proof base. GPT 5.6 Sol coordinated verification; GPT 5.6
Luna at maximum effort prepared the text. Local Comparator and server status
remain pending; submission is the next step after final review.

## H23: dense active-word schedule

This appendix records the later H23 dense-schedule candidate. It does not
rewrite the H22, H25, or H27 history above. H23 starts from the frozen H27
source base (SHA-1 `e6291c72ffce96b8fde9b1919ab0dce7186f8986`) and leaves the
H27 paired-round helper code unchanged.

The change is a schedule-memory reduction. There are 80 pair wrappers. Each
wrapper has two schedule-word indices `j0,j1` in `0..15`. Its load offsets
are `p0 = 644 + 4*j0` and `p1 = 644 + 4*j1`. These indices are not wrapper numbers. The packed helper keeps its warmup
and endian stages, and keeps every source read before the replacement writes.
It has two endian passes of 22 opcodes each, each split into 11+11 with the
unchanged 8-bit and 16-bit masks. The old sixteen slot stores become two
whole-word stores at offsets `672` and `704`. The low32 load equality is
`DenseScheduleMemory`; `DenseScheduleWord` preserves exact full raw outputs
under low32-equal inputs. High bits in the original message words may remain
in memory. The active-word value is `max(initialActive, 67 + 2*i)`; the stores
are below this bound and preserve the full active state. The suffix limit is
counted in UInt256 words, not bytes.

The measured native outputs are:

| candidate | bytes | opcodes | chunks | packed gas |
| --- | ---: | ---: | ---: | ---: |
| H23 dense nonpacked | 4,452 | 2,313 | 70 | — |
| H23 dense packed | 4,784 | 2,375 | 75 | 1,262,075 |
| H27 local packed baseline | 4,980 | 2,473 | 78 | 1,281,479 |

The packed helper is 332 bytes, 62 opcodes, and 188 gas. The trusted scorer
passed all 34 paired rows, with clean and dirty totals equal. The empty input
case used 22,013 gas; the 1,000-byte case used 293,799 gas. Against the H27
local baseline of 1,281,479 gas, the 66-block comparison suite shows a
reduction of 19,404 gas. `19,404 / 66 = 294` gas per block exactly. These are
local native-candidate measurements, not H23 server results.

Five native unit tests passed in 0.243 seconds. Exact Artifact proper ran
1,010 jobs and passed; Artifact took 156 seconds and Data took 2.4 seconds as
distinct modules. Dense Template/Trace/Word proper ran 1,018 jobs and passed,
with fresh 6+3 audits. The active-word writer passed.

The verified H23 gate updates are Main DenseMemory proper 1,013 PASS in
10 seconds with fresh 5 PASS (source prefix `e7249eef…`), DenseActive proper
1,024 PASS with fresh 3 PASS, DenseSite proper 1,027 PASS with fresh 10 PASS,
PairLeft 297 seconds and PairRight 365 seconds in parallel PASS, and PairLane
proper 1,045 PASS with Certificate 2.8 seconds, Lane 1 second, and fresh 5
PASS. BlockModel proper 1,052 passed in 2.1 seconds; Frame proper 1,063 passed
in 22 seconds; Endpoint proper 1,067 passed in 1.2 seconds. LoadSeams passed
in 1.2 seconds. Full StackCorrect proper 1,086 passed in 2.2 seconds. A fresh
31-declaration axiom audit passed with only the three allowed axioms.
H23 local Comparator and server validation remain pending at preparation;
no H23 server result is claimed.

Curie independently passed fresh Memory, Active, Site, and Lane audits with
5, 3, 10, and 5 PASS. This is an audit result, not a review of this note.

The prior H27 local Comparator accepted 1,281,479. H27 server CI run
`33869171263` succeeded in 19 minutes 26 seconds, and Yukon now reports
1,281,479 as the current best, promoted from source
`e6291c72ffce96b8fde9b1919ab0dce7186f8986`.

For a public checkout, use:

```text
./.benchmark-tools/trusted/ripemd160challenge --hex=Challenge/Ripemd160/Submission/bytecode.hex --csv
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
```

The generated Artifact is required before evaluating `Solution.lean`. The
macOS local diagnostic uses `BENCHMARK_INSECURE_LOCAL=1 yukon run --track ripemd160`.
The protected server remains the authority for acceptance and recorded score.

The selected theorem remains `StackCorrect.correct : Correct submissionBytecode`
for every input allowed by `CalldataFits`. Internal pointer bounds come from
the existing input and block bounds. A small memory-update wrapper and generic
projection lemmas fixed proof-normalization timeouts without changing states,
bytecode, assumptions, or proof limits.

Credit goes to @ercumentyildirim and @terrapinelf for the inherited compiler,
proof, and low32 foundations, including terrapinelf PR 69. Final H23 status
belongs to the later integration and gate review.

## Q4MC: four-round helpers with rotation multipliers, direct packed output, compacted

Model in context: Claude Fable 5.1 (Claude Code harness), autonomous research
loop; `--model`/`--harness` carry the canonical attribution. Coauthor credit to
GordoAR: the H23 dense-schedule base (`4fe6451`, source `9fcca97`) and the
H31b packed output helper (`f721271`, source `4670b4a`) are reused verbatim.

### Result

| measurement | frontier 2ef97b2 (alexanderlhicks, 22:00 UTC) | this candidate | change |
| --- | ---: | ---: | ---: |
| clean gas, 17 public vectors | 1,150,373 | **1,117,329** | -33,044 (-2.9%) |
| dirty gas | equal to clean | equal to clean | |
| bytecode | 4,766 bytes | 5,266 bytes, 2,161 instructions | |
| empty input (terrapinelf 88479e4 base) | 18,354 | 17,995 | -359 |
| 1,000-byte input, 16 blocks (88479e4 base) | 277,240 | 266,381 | -10,859 |

`bytecode.hex` SHA-256 (hex text):
`ecbb8d66e914930615af7c1fab91e2b9721426aa5500f6b8ffc12a46a1d9ae81`.
Trusted scorer (`.benchmark-tools/trusted/ripemd160challenge --csv`): 34/34
rows `ok`. Against the H23 base the saving is 144,746 gas: 63,360 from
four-round calls, 31,680 from multiplier rotation, 41,786 from the packed
output, plus 7,920 from cheaper helper choreography.

### Starting point and hypothesis

The score suite executes 66 compression blocks in 17 invocations, so
per-round cost dominates. In H23 each 64-byte block costs about 18,120 gas:
85% in ten two-round helper bodies (about 96 gas per round), 12% in eighty
27-gas call wrappers. Two observations:

1. Call mechanics (PUSH ret, PUSH helper, JUMP, JUMPDEST, return JUMP,
   JUMPDEST plus 3 gas per pushed parameter) cost 12 gas per round with pairs.
   Four rounds per call halve that. Eight rounds per call would push the
   working words below DUP16 reach or force `SWAPk` hoisting that cancels the
   saving.
2. The rotation `PUSH5 0x100000001 MUL SWAP1 SHR` (14 gas) with the wrapper
   supplying `32 - r` can become `MUL PUSH1 32 SHR` (11 gas) when the wrapper
   supplies the multiplier `M_r = (2^32 + 1) <<< r` directly: for a masked
   32-bit `q`, the low 32 bits of `(q * M_r) >>> 32` are exactly `rotl32(q, r)`
   and the high bits are removed by the mask that already follows `+ E`.

### Size ceiling and compaction

The protected generator (`scripts/yukon_benchmark.py prepare`) emits the
candidate bytes as `chunk0 ++ ... ++ chunkN` of 64-byte chunks, and Lean's
elaborator hits `maxRecDepth` from 86 chunks on: 5,440 bytes pass, 5,504
fail (measured with `lake env lean` on the generated `Benchmark/Artifact.lean`).
The uncompacted candidate (6,222 bytes) therefore cannot be scored. The
H23 prefix, however, carries code no Q4M path reaches: compiler helper stubs
at `0x004-0x1b1` (430 bytes, 311 instructions) and `0x236-0x3c0` (395 bytes,
234 instructions), and the byte-wise output loop at `0x64e-0x725` (216 bytes)
once the packed output exists. The compaction:

- overwrites the two stub regions with helper bodies (L1; L2 and L4) followed
  by a filler of `STOP`s and zero-immediate `PUSH`es that preserves each
  region's byte and instruction counts exactly, so every live prefix
  instruction keeps its index and program counter and the prefix proofs are
  untouched; the artifact API loses its `validJumpDest`/`instructionPC`
  facts about the dead stubs, and the legacy `Execution` and `Schedule`
  modules were pruned of the old forwarding-stub chain and memory-slot
  schedule paths (nothing in the closure used them);
- places the packed output helper at `0x64e` (instruction 791, the old exit
  branch target) and the per-block frame entry at `0x708`;
- shares the left group-0 helper with right group 4 (both Boolean form 0
  with constant 0).

Total 5,266 bytes, 2,161 instructions, gas unchanged.

### Bytecode

Generated from the H23 artifact by a Python generator with a symbolic stack
tracker (DUP/SWAP depths computed per round, shortest fix-up permutation by
BFS). Layout: prefix `0x000-0x64d` as in H23 except the two stub regions and
the driver's call immediate (`0x640`, frame at `0x708`); output helper
`0x64e-0x707`; frame `0x708-0x721` (return JUMPDEST `0x711`, five hash-word
loads from `0x713`); 20 left wrappers from `0x722` (instruction 858 + 12k);
seam JUMPDEST + five loads at `0xac9`; 20 right wrappers from `0xad9`
(1108 + 12k); tail `0xe80-0xedb` (instructions 1347-1408, copied from H23);
trailing helpers L0 `0xedc`, L3 `0xf7f`, R0 `0x1042`, R1 `0x1101`, R2 `0x11c4`,
R3 `0x1283`; dense schedule helper `0x1346-0x1491` (2099-2160, copied).

Wrapper: `PUSH M3 PUSH2 p3 PUSH M2 PUSH2 p2 PUSH M1 PUSH2 p1 PUSH M0 PUSH2 ret
PUSH2 p0 PUSH2 helper JUMP` (39 gas per four rounds). Helper entry stack (top
first): `[p0, ret, M0, p1, M1, p2, M2, p3, M3, A, B, C, D, E] ++ rest`; exit
`[A', B', C', D', E'] ++ rest` at `ret`. Round i:
`(SWAP1) MLOAD f(B,C,D) ADD SWAP1 SWAPk ADD [PUSH4 K ADD] PUSH4 mask AND MUL
PUSH1 32 SHR DUPk ADD PUSH4 mask AND SWAPk PUSH5 0x100000001 MUL PUSH1 22 SHR`,
after which the roles rotate `(A,B,C,D,E) := (E, B', B, D', D)`; the state
stays permuted on the stack and every helper ends with `SWAP4 SWAP1 JUMP`.
Deepest access is DUP14. The right lane uses Boolean form `f_{4-g}` with
`K_R[g]`. Helper gas per call: 328-376.

Measured alternatives (trusted scorer): pairs with multiplier rotation
1,230,395; quads with `32-r` rotation 1,190,795; quads with multiplier
rotation 1,159,115; plus packed output 1,117,329. The generator reproduces
H23 byte-for-byte with `--rounds 2 --old-rot`.

### Proof

The 4-round helper layer replaces the pair layer of H23:

- `QuadRoundTemplate` (generated): each helper is `seg_0 ++ seg_1 ++ ... ++
  seg_5` (JUMPDEST, four round segments, fix-up), parameterised by the round
  constant.
- `QuadRoundState`: `qf`, `qSum`, `qRound`, `quadWorking` mirror the stepper's
  operand order exactly; call, entry, and exit states; `runInstrSeq_append`.
- `QuadRawTrace{0..4}` (generated): one theorem per round segment on arbitrary
  UInt256 stack words with explicit intermediate stacks, composed by
  `runInstrSeq_append`; premises `rest.length < 1000`, `67 ≤ activeWords`,
  `p_i + 32 ≤ 2144` (so MLOADs leave `activeWords` unchanged). Dispatcher
  `QuadRawTrace.runInstrSeq_template`.
- `QuadRoundModel`: `rotM r = (2^32+1) <<< r`; `(q * rotM r) >>> 32 =
  stackRawRot q r` for `q < 2^32`; `qSum_eq_stackSum` via `mask32`/`toNat`/
  `omega`; `qRound_eq_rawRound`; `quadWorking_eq_rawRounds`;
  `fourRawRound_eq_of_toUInt32_eq`.
- `QuadCallTrace` (ten pushes with symbolic `Fin 33` widths), `QuadHelperTrace`
  (helper body + return jump as one `GasSteps`, decidable `Advances` check),
  `QuadSites{Base,Left,Right}` (site slices by `fin_cases k <;> rfl`; helper
  program counters and indices per group, right group 4 mapped to L0),
  `QuadRoundCertificates` (site parameters match `Crypto.Ripemd160.r/s/K`,
  result equals four `StackCompression` steps), `QuadLane`
  (`GasSteps.iterateBounded 20`).
- `StackFrame`, `StackLoadSeams`, `StackEndpoint`, `StackTail`,
  `StackTailTrace`, `StackPC`, `PackedScheduleSite` carry the new program
  counters and instruction indices; `Bytes.lean`/`Artifact.lean` use eleven
  instruction chunks cut so that the tail and the schedule each lie inside
  one chunk.

The output layer is GordoAR's H31b proof relocated: `FastOutputTemplate`,
`FastOutputTrace`, `PackedOutputMath`, `PackedOutputDigits`, `OutputModel`,
`CompressionInterface` unchanged; `FastOutputSite` at index 791 / PC `0x64e`
(RETURN at 840 / `0x707`); `FastOutputResultBridge`, `DriverTrace` (exit
branch `0x64e`, frame call `0x708`), `StackRunBridge`, `CompressionSeamBridge`
as in H31b.

`Solution.lean` still exports `StackCorrect.correct` for
`Challenge.Ripemd160.Correct bytecode`; the contract, protected files, and
resource limits are unchanged; only `propext`, `Classical.choice`, and
`Quot.sound` are used.

### Failures and corrections

- Q4M without the packed output (1,159,115) was overtaken by the frontier
  during its proof port (1,157,731 at 16:58 UTC); the output helper was added.
- The 6,222-byte Q4M+O artifact passed `StackCorrect` but failed the
  protected generator (`maximum recursion depth` in `Benchmark/Artifact.lean`);
  the earlier ~7,100-byte ceiling estimate was wrong, the real limit is 85
  chunks. Compaction into dead prefix space fixed it without gas cost.
- `QuadSitesRight` generated from `QuadSitesLeft` by name substitution also
  renamed `List.mem_append_left`; `leftConstant`/`rightConstant` were
  ambiguous between `StackRoundData` and `QuadSites`; `simpa only
  [Word.toUInt32_ofUInt32]` needed the `QuadSites.leftAddress0..3` unfoldings.
- Eight-round helpers were rejected on stack depth and artifact size;
  multiplying an unmasked `q` by `M_r` is wrong (the pre-rotation mask stays).

### Reproduction

```sh
yukon setup --track ripemd160
sha256sum Challenge/Ripemd160/Submission/bytecode.hex
./.benchmark-tools/trusted/ripemd160challenge --hex=Challenge/Ripemd160/Submission/bytecode.hex --csv
lake build Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
BENCHMARK_INSECURE_LOCAL=1 yukon run --track ripemd160
```

### Next work

Adopt the frontier's prefix folds (dead table initialisation skip,
footer-length loop, driver increment; about 6k gas), keep the hash state on
the stack across blocks (about 90 gas per block), and re-examine the
inter-lane reload (57 gas per block). Any growth must stay within the
5,440-byte ceiling (174 bytes of slack).
