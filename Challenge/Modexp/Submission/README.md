# Current refinement: single-test Fermat join (-181 gas per draw)

Base: promoted `be76a99a-6bdc-433f-9c2e-cc34523f4381` (juanbono, R5 1024-bit kernel).
Two dispatch blocks change; byte length (10,698), instruction count (8,543), every
byte PC and every pre-existing `JUMPDEST` are unchanged.

* Join guard at PC 33 (bytes 34..40): `DUP2 NOT DUP2 ADD PUSH1 1 LT` becomes
  `PUSH1 1 DUP3 ADD DUP2 XOR JUMPDEST`, i.e. `modulus XOR (exponent + 1)`. It is
  zero exactly when `exponent = modulus - 1`; the old `1 < modulus + ~exponent`
  also let `exponent = modulus - 2` (the BN254 inversion vector) detour through
  the special-prime test and a recheck at 4839 before the window route.
  `FermatNext.joinGuard_zero_iff` proves the guard equivalence without premises.
* PC 4839 (bytes 4840..4847): the recheck `DUP2 NOT DUP2 ADD PUSH2 0x02e9 JUMPI`
  is now `PUSH2 0x0000 POP JUMPDEST JUMPDEST JUMPDEST JUMPDEST`, an exact no-op;
  `FermatGas.handled` passes the join hypothesis to the unchanged Fermat result.

Seed-zero pinned-EVM total: 366,770 gas (44/44) versus 366,951 for the base;
the saving is the same 181 gas on every corpus seed (the changed bytes are not on
any RSA path). Local measurements are not an official score.

---

# Current refinement #115: estimator increment

This version replaces byte PCs2504..2506 `NOT; PUSH0; SUB` with
`PUSH1 1; ADD`. The modular UInt256 identity is universal, including wraparound:
`1 + x = 0 - NOT(x)`. Both byte strings are three bytes; the new image has
11,156 bytes and 9,187 decoded instructions. Existing JUMPDEST PCs and all
following instruction byte PCs are unchanged. Instruction indices starting at
old index1955 move down one and their artifact proof bindings are updated.

Matched seed-zero executable measurements: 374,391 gas, 44/44 correct, versus
374,399 for local #114 (now submitted as
`8209e460-f3f8-4abb-baba-5e14f082044b`) and 374,457 for accepted #105 on that same
corpus. This is not a direct comparison to hosted official scores. The current
hosted frontier remains 373,913 until a new official result is returned.

`Proofs/CycleGlobal/ShiftTrace1.lean` proves the word identity and the exact
`run_negDoneB` state transition with the inherited theorem contract. The focused
artifact-bound build passed; the full protected local gate and hosted status
are documented separately in the submission note and receipt. No proof trust
exception, runtime special case, scorer change, or vector-specific route is used.

Decoded byte SHA-256:
`bea8ea1aa6ea98eb602d509b1097075d3212fb89503699c4012f61b123f87573`.

Run the repository's documented local gate with:
`BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh modexp`.
It explicitly uses Comparator's insecure local sandbox here, so only an actual
Yukon evaluation can establish an official result. Prior documentation follows
as historical provenance and does not describe the current byte count/hash.

---

# MODEXP: cycle normalizer dead-code elimination

Development base: accepted aerugo-ef v15, commit
`bb2353349ec3854333007e928ef0e4be8843c243`.

The exact executable is 11,156 bytes (8 bytes smaller). In the radix-240
normalizer, eliminate the initial addition of zero and the final borrow
comparison, whose bit is discarded after the top-digit subtraction. Adjust
the terminal stack exchange to skip the removed dead slot. No carry or borrow
assumption is introduced: the modified execution theorem accepts the same
arbitrary word arguments as the original.

The 44 public seed-zero vectors all return the correct result at **374,465
gas**, versus **374,487** for the direct parent (22 gas saved). These are local
pinned-EVM measurements, not an official score. The RSA-2048 e=3 vector improves
from 22,657 to 22,635 gas; the other 43 are unchanged. The optimization saves 22
gas per normalizer invocation, not per MODEXP call. A separate full-program
near-maximum-modulus witness with N=2^2048-3, base=N-1 and exponent=3 returns the
correct value for both images, at 23,489 versus 23,467 gas.

## Proof binding

`Proofs/Cycle/NormalizeExecution.lean` proves the modified exact instruction
sequence with no additional hypotheses. `NormalizeMeaning.lean` and
`NormalizeBinding.lean` connect it to the unchanged word-subtraction meaning.
`Proofs/Cycle/Artifact.lean` assembles the 9,189 instructions to the exact
literal in `Proofs/Cycle/Bytes.lean`. Existing cycle/caller/global correctness
then feeds `Solution.lean` and the protected benchmark artifact. The allowed
axiom set remains `propext`, `Classical.choice`, `Quot.sound`.

Run `BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh modexp` for the documented local
Comparator and gas gate. Local execution uses the documented fake sandbox and
is not a ranked verification. The full gate result is recorded in the attached
research report; this README is not itself an acceptance receipt.

Decoded byte SHA-256:
`4a43d5e6471264bf96ca8df6229ba175c9539ef16920697b32171bd63a789d5e`.

## Attribution

This refinement builds directly on aerugo-ef v15 (GPT-6 Astra / Codex), the
retained v14 lineage, fkiene's compatible public refinements, and Th0rgal's
Gemini 3.1 Pro / Antigravity schedules. Claude's original contribution and all
inherited provenance and Apache 2.0 notices are preserved below and in the
provenance files. This iteration adds only the normalizer dead-code elimination
and exact proof/artifact integration. See `dependencies.json`.

---

## Inherited v15 documentation

# MODEXP: retain radix-240 values across repeated operations

This v15 candidate uses 374,487 gas on the 44 public seed-zero vectors,
versus 392,554 for fkiene's `de134b66-a42c-4b03-a575-3f9318a88ad8` on the same
inputs: 18,067 gas saved (4.60%). The executable is 11,164 bytes.

The eight-word route retains nine radix-240 digits across repeated Montgomery
squares and the terminal product. Joint operand lifetimes, instruction
scheduling, memory reuse and finalization reduce repeated conversion and
storage work. The four-word setup also specializes its known buffer pointer.

## Verification

`Solution.lean` connects the exact protected literal rendered from
`bytecode.hex` to `CycleSubmission.Global.correct`. The theorem covers every
valid padded MODEXP input, including the general fallback, given sufficient
gas. The proof uses only `propext`, `Classical.choice` and `Quot.sound`.

The main proof layers are:

- `Proofs/Cycle/Core.lean`: repeated arithmetic, normalization and output.
- `Proofs/CycleCaller/Spec.lean`: eight-word caller and operand encodings.
- `Proofs/CycleGlobal/Correct.lean`: dispatch, conversion, both widths and fallback.

From the challenge root, run `./setup.sh modexp`, then `./benchmark.sh modexp`.
The documented local mode is `BENCHMARK_INSECURE_LOCAL=1 ./benchmark.sh modexp`.

Decoded executable SHA-256:
`b158452c8397c428e5a13c0757c453b0462345ce11005604d9e3dee899f7b4e8`.

## Attribution and license

Claude found the original optimization in aerugo-ef's repository. This work
builds on aerugo-ef v14 and fkiene's compatible public refinements. Th0rgal's
Gemini 3.1 Pro / Antigravity schedules and other inherited implementations are
credited in the retained provenance. The new cycle, scheduling and proof
integration were developed with GPT-6 Astra / Codex.

`dependencies.json` declares direct dependencies. `INHERITED_PROVENANCE.json`
and `Provenance/` preserve the v14 declarations, attribution and historical
documents; their measurements and implementation descriptions refer to those
earlier versions. Original local work uses Apache 2.0; see `LICENSE` and the
upstream notices retained in the source.

## Fixed-caller decrement scheduling (iteration 105)

The cycle fixed caller at PC 2369 previously computed `k-1` by
`PUSH0; NOT; DUP3; ADD`. It now uses `PUSH1 1; DUP3; SUB`.
Both sequences are four bytes; the new one saves 2 gas and one instruction.
The existing `1 <= k <= 16` caller conditions are unchanged. Both four-word
and eight-word caller lemmas use the same subtraction fact, with no new
arithmetic premise. No byte address or jump literal moves.

The full artifact remains 11,156 bytes and has 9,188 instructions.
Instruction indexes after the caller decrease by one. The concrete block
slices, located-instruction records, CLZ decoder, suffix base, and prefix-width
bridge are rebound to the exact new artifact; retained legacy bytecode modules
remain unchanged.

Matched local seed-zero EVM runs (44/44 correct in each batch): promoted v15
bytes 374,487 gas; normalizer-only parent 374,465; this revision 374,457.
Each of the four RSA-1024/2048 e=3/65537 vectors saves 2 gas versus the parent;
40 other vectors are unchanged. The promoted official score is 374,737 on a
different evaluation configuration; 280 is not a matched measured saving.
Local gas and local fake-sandbox Comparator acceptance are not official
leaderboard promotion.


### Current frontier checkpoint during iteration 105

The normalizer-only parent `84b3089d-b76a-43ea-907e-0d4357e4f387` was accepted
and promoted at official score **374,193**, source
`8f8a0b2c59e8f761088c97b21a6f4099a67305e1`. Its complete editable Submission
tree is identical to local `429f6dae`. Against that exact current frontier,
the caller revision saves **8 gas** on the matched public seed-zero corpus
(374,465 → 374,457); 30 gas is the combined local saving versus preceding v15.
Do not subtract the local 374,457 from official 374,193: these are different
corpus configurations. The new caller revision still needs its own official
validation. This checkpoint changes only documentation/attribution metadata;
all Lean sources and executable bytes remain frozen for the running gate.


## Shared-complement dispatch predicate (iteration 109)

The modulus-tail dispatch at byte PCs 631..640 now uses
`NOT; DUP1; ISZERO; SWAP1; JUMPDEST; PUSH1 1; AND; OR; JUMPDEST`.
The old sequence was
`DUP1; PUSH0; NOT; EQ; SWAP1; PUSH1 1; AND; ISZERO; OR`.
The new sequence shares the complemented input word between the all-ones
and low-parity tests. For every UInt256 input x, `~x == 0` iff x is the
all-ones word and `(~x & 1)` equals `ISZERO(x & 1)`.
The two sequential JUMPDEST instructions keep all 9,188 instruction indexes,
widths and byte PCs identical to the caller-decrement parent. The PUSH1 at
instruction 449 remains at byte PC 636. No existing destination literal moves.
`PredicateIdentity.lean` proves these scalar identities without premises;
`FastP1.lean` and `Setup.lean` bind the exact dispatcher and preserve all
existing pass and bailout hypotheses, including the inverse precondition.

On the pinned public seed-zero corpus, all 44 vectors are correct at
**374,445 gas**, versus 374,457 for the caller-decrement parent and 374,465
for the promoted normalizer image. Four generated RSA vectors each save
three gas; the other 40 are unchanged. These are matched local totals, not
an official hosted score. The normalizer's official 374,193 is from a
different corpus configuration and must not be mixed with local figures.

Decoded bytecode SHA-256:
`2cbd6189e98e0064602f00dcfe6db4544aa00282a0fbcf67a3bc2683c743d2f5`.
The isolated small gate built dispatcher Setup successfully (1,361 jobs).
Whole-program Comparator and scoring must independently accept this image;
this README alone is not an acceptance receipt. No carry shortcut, test-only
restriction, new axiom, or weakened premise is part of this change.
The caller-decrement parent was submitted separately as
`d1c8717a-46f1-468d-bd74-0eca2543d705`; its hosted validation was still pending
when this proof gate began. All earlier provenance and license notices remain.


## Sentinel-backed quotient-estimate mask (#112)

This revision additionally replaces bytes 2778..2781, `155f0317` with
`8201175b`: `ISZERO; PUSH0; SUB; OR` becomes
`DUP3; ADD; OR; JUMPDEST`. The all-ones sentinel was already on the entry
stack and is preserved. For a comparison bit b, `maxWord + b = 0 - isZero b`
in UInt256 arithmetic. The quotient word ORed with this mask is unrestricted.
The four one-byte instructions preserve every instruction index, width and
byte PC. The final JUMPDEST is padding (1 gas); the old window costs 11 gas
and the new window 10, saving one gas per estimate.

The parent is #109 (shared-complement dispatch predicate), commit
`b6484e8db9af2040ca06d991ac590ba7e6f0f6bd`, which includes caller-decrement #105.
The pinned public seed-zero batch measures **374,424 gas** for #112 versus
**374,445** for #109: 21 gas saved, 44/44 correct. These are local measurements,
not a hosted official score. Versus #105's 374,457, the cumulative saving is 33.

`CycleGlobal/ShiftPaths.lean` binds the changed instructions to the artifact;
`ShiftTrace2.run_estimate` proves the same result with the same premises.
No arithmetic or input restriction is added. The separate report theorem
`SentinelMask112.same_state` proves equality of the gas-erased instruction
runner's full Option State result with the explicit sentinel entry frame;
it does not assert equal remaining runtime gas. Exact decoded artifact:
11,156 bytes, 9,188 instructions, SHA-256
`3c753cd7874508334df1ebe2b555deea4ad0eb5e9359e42abf3c206f2a36d655`.
At this checkpoint the artifact-bound ShiftTrace2 proof passes; submission-level
Comparator and scoring remain mandatory and are recorded separately.


## Consumed dispatcher inequality condition (#113)

Replace PCs 2393..2394, `EQ; ISZERO` with `XOR; JUMPDEST`, retaining the
following `PUSH1 219; JUMPI`. XOR is zero iff its operands are equal. Since
the branch consumes the entire condition, preserving zero/nonzero truth is
sufficient; numeric equality of intermediate conditions is neither claimed
nor needed. `ShiftTrace1.dispatch_xor_isTrue` proves this for arbitrary words
and `run_dispatch` keeps the inherited premises. Artifact-bound ShiftTrace1
build: 1,385 jobs clean. Pinned combined public result: 374,416 gas, 44/44,
8 gas lower than #112 and 41 lower than #105 on the same seed-zero batch.
The artifact is 11,156 bytes / 9,188 instructions, decoded SHA-256
`103eb09ad3db35e38ab34bd7c95621e35a5ed4127b25868031a459e133104d30`.
A separate protected submission-level gate is required for this exact image.


## First-row carried-zero elimination (#114)

At PCs 4221..4226 replace `958510019450` with `505093831093`, i.e.
`SWAP6; DUP6; LT; ADD; SWAP5; POP` with
`POP; POP; SWAP4; DUP4; LT; SWAP4`. This removes addition of the carried
zero produced by the actual `PUSH0` at PC4131. The unsigned overflow
comparison `LT (p4+c) p4` remains intact for arbitrary wrapped sums.
`R4InlineRedt0.run_redt_0Zero114` proves the new schedule, and
`R4InlineBlocks.block_redt_0Zero114` binds it to the changed artifact.
`R4InlineTrace.gasSteps_red0Zero114` composes the entire zero-preserving
reduction, leaving the outer `gasSteps_core` statement unchanged.
Artifact-bound trace build: 1,470 jobs completed. Pinned EVM result:
374,399 gas / 44 correct, versus #113 374,416 on the same public batch.
There is no arbitrary-carried-word equivalence claim. All PCs and widths
are preserved; artifact remains 11,156 bytes / 9,188 instructions,
decoded SHA-256 `9edcd83a2c11e5969ac326c1d37338ca830481b0be998c65bea8bb0cec4ff5f4`.
