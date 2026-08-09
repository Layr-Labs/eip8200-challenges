# SHA-256 optimization experiment ledger

This is the live decision log for the verified raw-EVM SHA-256 candidate.
It exists to make experiments reproducible, preserve failed approaches, and
keep proof cost proportional to measured runtime value.

Development context: GPT 5.6 Sol, xhigh effort, Codex agent.

## 2026-08-09: bounded loop guards after paired-round promotion

The preceding paired-round candidate was submitted as
`e92b37f8-807a-4330-8f0d-9c39f18130b4` and subsequently passed remote
validation. Yukon promoted it at score 2,970,647, so the two-round
virtual-midpoint architecture is now a confirmed frontier checkpoint rather
than only a local result.

This follow-up deliberately kept that architecture and its semantic
boundaries unchanged. It targets three loop guards and uses three unreachable
post-jump locations as structural-instruction reservoirs. The candidate file
is still exactly 1,524 bytes and its decoded artifact is still exactly 810
instructions. The ASCII hex file SHA-256 is
`430db430149e11663b4c13ba357dedb1a19d970347249edcd32bb7a5445fb3a6`;
the SHA-256 of the 1,524 raw bytes is
`813ac641bd57eb252c3097db2cadbdc07b6bee493bc88b205c28c2c4259dd7ab`.

### Exact byte changes

Six length-preserving edits were made:

1. At PC `0x1ab`, `64000000018e56` became `630000018e5600`.
   The live value 398 is encoded by `PUSH4` instead of `PUSH5`; the freed byte
   becomes an unreachable `STOP` after the unconditional `JUMP`. This adds one
   decoded reservoir instruction without changing live gas.
2. At PC `0x1c1`, `6010811015` became `6100108114`. The initializer condition
   `(j < 16) == 0` becomes `j == 16`. Its induction invariant proves
   `0 <= j <= 16`, so equality is equivalent at every reachable check. The
   new condition saves three gas and one instruction on each of 17 checks.
3. At PC `0x27e`, `5b6103a7` became `620003a7`. A sequential `JUMPDEST` and
   `PUSH2 935` become one `PUSH3 935`, saving one gas and one instruction on
   all 32 live pair iterations plus the exit check.
4. At PC `0x388`, the unreachable `PUSH30 0` filler becomes `PUSH29 0; STOP`.
   This restores one structural instruction with no live execution.
5. At PC `0x3af`, `5b6103e1` became `620003e1`. The same coalescing turns the
   feed-forward guard's sequential `JUMPDEST; PUSH2 993` into `PUSH3 993`,
   saving one gas across eight iterations plus the exit check.
6. At PC `0x3d8`, `66000000000003aa56` became `650000000003aa5600`.
   `PUSH7 938` narrows to `PUSH6 938`; the final byte is an unreachable
   `STOP` after the unconditional `JUMP`, balancing the last removed live
   instruction.

The arithmetic is exact. The initializer change saves `3 * 17 = 51` gas per
padded block, the paired-round guard saves 33, and the feed-forward guard
saves 9. Total improvement is therefore 93 gas per block. The public suite
contains 65 padded blocks, so the measured suite improvement is
`93 * 65 = 6,045`: 2,970,647 becomes **2,964,602**. Empty-input gas falls from
46,691 to 46,598.

### Verification and proof changes

Native falsification was run before proof work. The trusted scorer reported
all 19 clean rows and all 19 dirty-frame rows `ok`, with identical gas for
each clean/dirty pair. The clean total was exactly 2,964,602.

`Bytes.lean` was regenerated to the exact hex and `Artifact.lean` was updated
at the six spans. Its assembly theorem reduces by `rfl`, certifying that the
810 located instructions assemble to the current byte string. The initializer
trace now proves the bounded equality guard. The compression pair paths and
feed-forward paths were reindexed around the removed sequential jump
destinations and added unreachable stops. Direct block proofs, pair
composition, compression composition, pair correctness, driver correctness,
and the final `ReferenceCorrect` theorem were all rebuilt from source.

One build-system trap was recorded: invoking `lake env lean` on an individual
file can consume stale dependency oleans, whereas `lake build <module>` first
refreshes `Bytes`, `Bytecode`, and the artifact. The apparent assembly failure
disappeared once the dependency graph was rebuilt normally. Optional internal
gas-summary modules are not part of the exported comparator theorem; Yukon
uses its trusted scorer for ranking. Time was therefore spent on the actual
`ReferenceCorrect` acceptance path rather than delaying submission on an
unused duplicate gas model.

The full official local command was:

```text
BENCHMARK_INSECURE_LOCAL=1 yukon run
```

It reported:

| Check | Result |
|---|---:|
| Lean submission build | accepted |
| Lean default kernel | accepted |
| Comparator | accepted |
| Correctness vectors | 19/19 |
| Verified score | **2,964,602** |
| Bytecode size | 1,524 bytes |
| Structural instructions | 810 |

The next architectural investigation should preserve this proof-complete
checkpoint while testing whether a four-round superstep, a phase-rotated H
layout, or a schedule/compression fusion produces a larger native win without
exceeding standard `DUP16`/`SWAP16` reach. Any candidate should first be
tested in a temporary byte artifact against all clean and dirty vectors before
its proof surface is promoted into the workspace.

Development context: GPT 5.6 Sol, xhigh effort, Codex agent.

## 2026-08-08: four direct recurrence schedule loads — native verified

The four hot recurrence reads of `W[j-16]`, `W[j-15]`, `W[j-7]`, and
`W[j-2]` now load from memory directly instead of entering the generic `wAt`
accessor. Each address is folded to `base + (j << 5)`, with adjusted bases
288, 320, 576, and 736. For `16 ≤ j < 64`, these are exactly the existing
schedule slots `(j-k) * 32 + 800`.

Every replacement retains its original byte length and structural instruction
count by widening the base to `PUSH4` and retaining an executed `JUMPDEST` at
the local boundary. All later PCs, semantic states, and the 1,524-byte,
810-instruction artifact remain stable. The generic accessor proof legs are
removed from the recurrence composition; four direct execution lemmas end in
the existing `gotW16`, `gotW15`, `gotW7`, and `gotW2` states.

Each direct path saves 38 gas, or 152 gas per recurrence iteration. Across 48
iterations this is 7,296 gas per padded block and 474,240 over the public
65-block suite. The protected native scorer accepts all clean and dirty rows
with identical paired gas: exact score 4,674,887 and empty-vector gas 73,179.
The exact schedule cost falls from 36,250 to 28,954, compression from 78,609
to 71,313, and the driver from 78,684 to 71,388 gas per padded block.

## 2026-08-08: fused `BSIG0` and `BSIG1` helpers — native verified

Both big-sigma helpers now duplicate the input's 32-bit lane once and derive
their three rotations through chained right shifts. `BSIG0` uses shifts
2, then 11, then 9; `BSIG1` uses 6, then 5, then 14. Masking the resulting XOR
is universally equivalent to rotations 2/13/22 and 6/11/25 respectively. The
Lean word proof establishes this identity for arbitrary 256-bit inputs, rather
than relying on a caller invariant that the high 224 bits are zero.

Each executed helper falls from 238 to 60 gas and each caller removes the
obsolete output placeholder for another 2 gas. Length- and
instruction-preserving unreachable padding keeps every later PC stable. The
pair saves 360 gas per round, 23,040 per padded block, and 1,497,600 over the
65-block suite. The protected native scorer accepts all clean and dirty rows
with identical paired gas: exact score 5,149,127 and empty-vector gas 80,475.
The candidate remains 1,524 bytes and 810 structural instructions.

## 2026-08-08: five fixed state load/store fusions — verified

The four remaining working-state shifts and the `h4 := h3 + t1` update now
perform their fixed-address `MLOAD` and `MSTORE` operations directly. This
removes the generic `hSet` setup, jump, return, and cleanup path that remained
after the fixed `hAt` loads were specialized. Widened `PUSH5` address literals
and unreachable `JUMPDEST` padding retain every enclosing byte span and
structural instruction count, so the candidate remains exactly 1,524 bytes and
810 instructions.

The raw execution proofs end in the existing `afterShift7`, `afterShift6`,
`afterStoreH4`, `afterShift3`, and `afterShift2` semantic states. The
composition proof therefore reuses the unchanged SHA-256 round correctness
layer. Exact gas proofs reduce the update phase from 359 to 179 gas, the round
from 1,179 to 999 gas, compression from 113,169 to 101,649 gas, and the driver
from 113,244 to 101,724 gas per padded block.

The protected native scorer accepts every clean and dirty vector with equal
paired gas. Each site saves 36 gas per round; the batch saves 11,520 gas per
padded block and 748,800 across the suite. The exact clean score is 6,646,727
and the empty vector costs 103,515 gas.

## 2026-08-08: inline variable-index `W[j]` load — verified

The compression round's hot message-schedule accessor call is now replaced by
an in-place address calculation and `MLOAD`. The old nine-byte sequence
`PUSH2 return; PUSH0; DUP5; PUSH2 wAt; JUMP` becomes `DUP3; PUSH1 5; SHL;
PUSH2 800; ADD; MLOAD`. It consumes the same round index semantically while
avoiding the accessor jump, return, and cleanup path.

The direct sequence has six structural instructions where the call had five.
To retain the benchmark's exact 810-instruction artifact as well as its
1,524-byte bytecode size, the unreachable six-byte pad following the direct
`h7` load was changed from `JUMPDEST; PUSH3 0; POP` to `PUSH4 0; POP`. The new
padding is still unreachable and preserves the next executed PC.

The raw execution proof establishes the dynamic memory address for every
round index, using the existing UInt256 word-add commutativity theorem to
bridge `800 + (j << 5)` with the semantic schedule layout `(j << 5) + 800`.
Composition now reaches `gotW` directly and no longer includes the generic
`wAt` certificate. Exact gas proofs establish T1 cost 487, round cost 1,215,
compression cost 115,473, and driver cost 115,548 per padded block. The direct
load saves 33 gas per round and padding compaction saves one more: 34 per
round, 2,176 per block, and 141,440 over the public suite.

The complete kernel build and protected native scorer pass. All 19 clean and
dirty vectors are `ok` with identical paired gas. Clean suite score is
7,545,287 and the empty vector costs 117,339 gas.

## 2026-08-08: seven fixed-index state loads — verified

The batch specialization of the seven remaining hot, fixed-index `hAt` calls
is now implemented and proof-complete locally. The exact sites load `h2` and
`h1` while forming T2, then `h6`, `h5`, `h3`, `h2`, and `h1` while shifting the
working state. Every ten-byte call setup was replaced by a direct memory load
plus unreachable padding, preserving bytecode length and all downstream PCs.

The candidate-specific execution lemmas now terminate directly in the existing
`loadReturned` semantic states. The composition proof no longer traverses the
seven generic accessor certificates. Exact gas proofs establish T2 cost 369,
updates cost 359, round cost 1,249, compression cost 117,649, and driver cost
117,724 per padded block. The protected native scorer reports all 19 clean and
dirty vectors `ok`, with equal gas in both frames, and a clean suite total of
7,686,727. This is 1,135,680 below the preceding h7 candidate.

## Operating loop

Every candidate follows the same gates:

1. Inspect the concrete bytecode call graph and exact execution frequency.
2. Form a length-preserving local rewrite whenever possible, so later PCs and
   embedded jump immediates stay stable.
3. Apply the rewrite to a temporary byte file first.
4. Run the protected scorer on all 19 vectors from clean and dirty VM states.
5. Abandon immediately if any status, output, or clean/dirty gas pairing fails.
6. Only after runtime confirmation, update reducible bytes, the structural
   artifact, localized raw-step paths, semantic composition, and gas proofs.
7. Build the smallest expensive leaf first. For compression changes this is
   `CompressionExec`; it costs about six minutes and catches PC/stack/memory
   mismatches before the larger dependency graph is rebuilt.
8. Build the complete `GasCost` theorem, freeze the exact current hex into the
   generated benchmark artifact, build `Solution`, and audit top-level axioms.
9. Submit immediately with a detailed public note and exact model attribution.
10. Continue experimenting while Yukon validates; validation latency is not a
    development blocker.

The accepted top-level axiom set is exactly `propext`, `Classical.choice`, and
`Quot.sound`. Any use of `native_decide` in the exported proof is rejected even
when executable behavior is correct.

## Results so far

| Stage | Exact score | Suite delta | Status / lesson |
|---|---:|---:|---|
| Protected reference | 10,179,119 | — | Initial baseline |
| Direct main entry | 10,175,927 | -3,192 | Skip 14 forwarding trampolines |
| Compression increment | 10,155,127 | -20,800 | Direct-add peephole |
| `Ch` + `Maj` schedules | 10,117,687 | -37,440 | Boolean identities, kernel-safe proof |
| All counter increments | 10,093,527 | -24,160 | Four more fixed-length peepholes |
| Duplicated-lane rotate | 9,868,887 | -224,640 | Two operations removed per rotate call |
| Consuming accessors | 9,309,127 | -559,760 | Largest promoted structural win so far |
| Direct fixed `h6` | 9,146,887 | -162,240 | Promoted; 39 gas per round |
| Direct fixed `h5` | 8,984,647 | -162,240 | Submitted, validating when logged |
| Direct fixed `h7` | 8,822,407 | -162,240 | Submitted, validating when logged |
| Seven remaining fixed loads | 7,686,727 | -1,135,680 | Proof-complete; submitted for validation |
| Inline variable `W[j]` load | 7,545,287 | -141,440 | Proof-complete; submitted for validation |
| Inline overlapping `K[j]` load | 7,395,527 | -149,760 | Proof-complete; submitted for validation |
| Five fixed state load/store fusions | 6,646,727 | -748,800 | Proof-complete; full Yukon gate running |
| Fused `BSIG0` + `BSIG1` helpers | 5,149,127 | -1,497,600 | Native scorer passed; universal proof integration running |
| Four direct recurrence schedule loads | 4,674,887 | -474,240 | Native scorer passed; exact proof integration running |

The cumulative runtime-verified improvement is 5,504,232 gas versus the reference
public score.

## What worked

### Preserve byte length and instruction count

Replacing an internal accessor call with direct `MLOAD` is only attractive if
it does not relocate hundreds of later PCs. The recurring ten-byte call body:

```text
PUSH2 return; PUSH0; PUSH1 index; PUSH2 hAt; JUMP
```

is replaced with:

```text
PUSH2 address; MLOAD; JUMPDEST; PUSH3 0; POP
```

Both spans contain five structural instructions and ten bytes. The executed
cost falls from a 19-gas setup plus the 32-gas consuming accessor to a 12-gas
direct load and neutral padding. Including the preceding caller `JUMPDEST`,
the complete path falls from 52 to 13 gas: 39 saved per use.

### Prove the semantic boundary, not all downstream code again

Each direct load is arranged to terminate in the already-defined accessor
return state such as `gotH6`, `gotH5`, or `gotH7`. A single raw-step theorem
proves the literal address equality and MLOAD result. The mature arithmetic,
state-update, loop, and SHA-256 specification proofs then reuse that semantic
boundary unchanged.

### Measure before proof investment

The protected scorer takes seconds; a raw compression proof takes minutes and
the full gas graph takes longer. Temporary exact-byte scoring has prevented
proof work on semantically invalid ideas and gives an exact target cost before
any arithmetic theorem is edited.

## Failures and course corrections

### Native decision procedures

Early `Ch` and `Maj` proof attempts used native evaluation to close concrete
bytecode equalities quickly. The functions were correct and their gas wins
were real, but the exported candidate inherited a disallowed native axiom.
Those submissions failed Comparator. The approach was abandoned and replaced
with reducible candidate-specific bytes and ordinary kernel reduction. The
same optimized helpers later promoted with only the three allowed axioms.

### Definitional equality with frozen reference bytes

The original proof succeeded because candidate bytes were definitionally the
protected reference. Even a one-immediate entry rewrite broke that shortcut.
Trying to transport the entire protected proof as if the bytes were unchanged
was a dead end. The durable solution was an editable candidate-specific proof
tree: reducible byte chunks, decoded structural artifact, localized traces,
semantic summaries, and exact gas composition.

### Stale PC tables

Length-preserving does not imply every instruction PC inside a rewritten span
is unchanged. Changing immediate widths can shift internal instruction starts
while preserving the next external boundary. The first direct-load proof lost
one six-minute replay to a stale internal PC entry. The process now explicitly
maps every structural index inside the span before starting Lean.

### Simplifier needs literal address facts

Direct MLOAD states use a literal offset such as 480, while the reusable
accessor-return state uses `288 + (index << 5)`. Lean did not always normalize
that equality automatically through active-memory calculations. A small
kernel-reducible lemma such as
`((ofNat 6).shiftLeft (ofNat 5) + ofNat 288).toNat = 480` closes both the
memory-read and high-water-mark obligations. This pattern is now added before
the first expensive replay.

### Memory high-water marks need an explicit invariant

The first `K[j]` proof attempts established the loaded word equality but left
64 identical active-memory goals, one for every round index. Enumerating the
indices only duplicated the same obligation. The final proof factors three
small lemmas: the earlier `W[j]` load expands memory beyond ten words, both K
windows end at or below byte 320, and a sub-320 load cannot expand an already
ten-word state. This closes every round uniformly and documents the modular
`UInt256` high-water conversion instead of relying on simplifier arithmetic.

## Current seven-load hypothesis

Call-graph inspection initially suggested that four state shifts used a
dynamic source index. The composition theorem revealed that the generic proof
function is instantiated at four distinct call sites with fixed sources 6, 5,
2, and 1. Therefore all remaining per-round loads are fixed:

| Site | State index | Address | Old return PC |
|---|---:|---:|---:|
| T2 first input | 2 | 352 | 753 |
| T2 second input | 1 | 320 | 764 |
| shift 7 ← 6 | 6 | 480 | 796 |
| shift 6 ← 5 | 5 | 448 | 817 |
| update `h4` from old `h3` | 3 | 384 | 849 |
| shift 3 ← 2 | 2 | 352 | 872 |
| shift 2 ← 1 | 1 | 320 | 893 |

Seven sites times 39 gas is 273 gas per round. Across 64 rounds this is 17,472
gas per padded block; across the 65 public blocks it is 1,135,680 gas. The
temporary exact-byte candidate passed every clean and dirty vector. Empty gas
fell from 136,987 to 119,515, exactly 17,472. The predicted suite score is
7,686,727.

## Next optimization direction

Fuse the shared `BSIG0` and `BSIG1` schedules around duplicated 32-bit lanes.
Temporary exact layouts preserve both helper spans, caller spans, all later
PCs, and the 810-instruction artifact. Each helper is projected to save 180 gas
per round; applying both would save another 1,497,600 gas over the suite.

## Fused small-sigma promotion

The schedule recurrence's `SSIG0` and `SSIG1` calls were promoted after exact
native testing on all clean and dirty vectors. Each helper now creates a
duplicated 32-bit lane once, obtains the second rotate by shifting the first
rotate, masks the rotate XOR once, and finally XORs the ordinary right-shift
term. Both callers use a two-word argument/return ABI and no longer push the
unused output placeholder.

The universal word proofs do not assume that the helper input is already
32-bit. They derive the chained shift identities with `Nat.shiftRight_add`,
rewrite the low lane with `evmRotr32_duplicate`, and prove the masked XOR
ordering explicitly. Direct helper traces then return the existing
`evmSmallSigma0` and `evmSmallSigma1` semantic values, leaving every downstream
schedule state unchanged.

Each old helper cost 176 gas; each fused helper costs 71 gas. Replacing the
placeholder `PUSH0` with a same-size executed `JUMPDEST` saves another gas at
each of the two callers. The exact improvement is therefore 212 gas per
recurrence iteration, 10,176 per padded block, and 661,440 over the 65-block
public suite. Native scoring is 4,013,447 with an empty-vector cost of 63,003;
all clean/dirty gas pairs are identical.

The next tested candidates are an unmasked low-32-congruent small-sigma
schedule at 3,907,367 and a direct recurrence store that combines with it at
3,838,727. Both have exact passing native artifacts; they remain deliberately
separate from this checkpoint so this universally masked version can reach the
frontier first.

## 2026-08-08: post-3,753,967 audit and specialized BSIG1 experiment

The current proof-complete checkpoint specializes BSIG0 through the T2
addition and mask. Its exact local and Yukon scores agree at 3,753,967, with
59,011 gas for the empty vector, 19/19 clean vectors, identical dirty-frame
costs, 1,524 bytecode bytes, and 810 structural instructions. Submission
`e2d09aee-566e-40cb-b721-b69fb49d1708` was queued while the next experiment
began; validation latency is deliberately treated as non-blocking.

The next component audit split each compression round into T1=271, T2=179,
and updates=180 gas. T1 still paid four distinct pieces around BSIG1:

| Piece | Current gas |
|---|---:|
| BSIG1 call setup | 21 |
| BSIG1 helper | 60 |
| direct `h7` load plus local pad | 12 |
| three additions and final mask | 13 |

BSIG1 has only this compression caller, so the experiment changed its ABI
from `[e, returnPC, Ch+K, W, mask, ...]` to `[e, Ch+K, W, mask, ...]`. The
helper computes the same raw chained rotations, adds `Ch+K` and `W`, directly
loads `h7` from byte address 512, adds it, masks the low word, and hard-jumps
to the existing T1 boundary at PC 725. PCs 725--729 become five executed
`JUMPDEST` instructions, allowing execution to fall through at the unchanged
PC 730 without relocating T2. A `PUSH7 0` plus five unreachable `STOP`s keeps
the 44-byte helper at exactly 29 structural instructions; the caller remains
11 bytes and seven instructions through an unreachable `PUSH2 0; STOP` pad.

This stream-only candidate was tested before editing any Lean file. The native
scorer accepted all 38 clean/dirty rows and preserved identical paired gas.
Empty gas fell from 59,011 to 58,307, exactly 704 gas per padded block or 11
gas per round. Across the public suite's 65 blocks the exact delta is 45,760,
for a projected score of **3,708,207**. The result proves the hypothesis and
justifies proof integration. The proof plan mirrors the already-landed BSIG0
specialization: add a T1-specific helper entry/return state, prove low-32
addition congruence from `fusedBigSigma1_eq`, replace the local execution path,
compose directly from `gotCh` to `afterT1`, then update T1 271->260, round
630->619, compression 57,145->56,441, and driver 57,220->56,516.

The alternative of moving the next T2 load into PCs 726--729 was considered
and rejected for this iteration. It could avoid the five 1-gas fall-through
destinations, but would shift every internal PC across T2 and require a much
larger artifact/proof relabel for only five additional gas per round. The
locally preserving version captures the reliable 11-gas win first; the more
aggressive packing remains a follow-up after promotion.

Proof integration completed successfully. The specialized helper executes a
direct `MLOAD 512` before the three additions so the resulting word matches
the existing left-associated T1 invariant without a global semantic rewrite.
The candidate-specific execution proof, compression composition, exact gas
cascade, and full exported `Solution.lean` certificate all compile. A complete
`BENCHMARK_INSECURE_LOCAL=1 yukon run` was accepted by the Lean default kernel
and Comparator with score **3,708,207**, 1,524 bytes, and 19/19 vectors. The
exact bytecode SHA-256 is
`866bd54740716ffc7e5226762cb1f6e821a9cade1c162be1d0dae95d9e549076`.

The follow-up landing-pad experiment retargeted the specialized BSIG1
helper's hard jump from PC 725 to the last existing landing instruction at
PC 729. PCs 725--728 are now unreachable `STOP` padding, while PC 729 remains
the single executed `JUMPDEST` before T2 begins at the unchanged PC 730. This
preserves every byte offset and structural instruction index while removing
four gas per round.

The native trusted scorer accepted all 38 clean/dirty rows with identical
paired gas. Empty gas fell from 58,307 to **58,051**, exactly 256 gas per
padded block. Across 64 rounds and the public suite's 65 padded blocks, the
exact score improvement is 16,640 gas. Full `BENCHMARK_INSECURE_LOCAL=1
yukon run` verification was accepted by the Lean default kernel and
Comparator at **3,691,567**, with 1,524 bytes and 19/19 vectors. The exact
bytecode SHA-256 is
`71aa7ea35c048153118966c4eaa64e0422a0079d0236252447d22d42e13cf421`.

## 2026-08-08: remove hot update padding

The five working-state update spans still executed thirty sequential
`JUMPDEST` padding instructions per compression round. Each fixed memory
address is now encoded with a wider `PUSH`, absorbing the same bytes while
removing those live no-ops. Thirty replacement structural instructions were
moved into unreachable small- and big-sigma helper padding, so all live byte
PCs, the 1,524-byte length, and the 810-instruction artifact remain fixed.

The trusted native scorer accepted all 38 clean and dirty runs with identical
paired gas. The exact score is **3,566,767**, down 124,800 gas from the prior
3,691,567 checkpoint: 30 gas per round, 1,920 gas per padded block, across 65
public-suite blocks. Empty-vector gas is **56,131**. The exact-gas proof uses a
fixed cost of 1,499 gas and 54,340 gas per padded block. `Bytes.lean`, the
assembled artifact, all execution and correctness layers, and `GasCost.lean`
compile successfully. The exact bytecode SHA-256 is
`c9226b74ed0b2bac66f593cbb2b1d5dce14c1d311fd1480747f349819580c32b`.

## 2026-08-08: bounded loop equality guards

Both live compression loops have exact proved bounds. The 64-round guard and
the eight-word feed-forward guard therefore replace `(i < bound) == 0` with
`i == bound`. Each ten-byte, seven-instruction span uses a sequential
`JUMPDEST` to preserve byte PCs and structural indices while eliminating one
executed `ISZERO`.

The trusted scorer accepted all 38 clean/dirty runs at **3,557,147**, with
identical paired gas and an empty-vector cost of **55,983**. The improvement is
9,620 suite gas, or 148 gas per padded block. The revised exact-gas proof uses
1,499 fixed gas and 54,192 gas per padded block; the complete artifact,
execution, correctness, and gas theorem builds are green. The exact bytecode
SHA-256 is
`e19051f32b98e2428a4ec69d54e799136da78bf71b7236d9f6f70ec7e1fe9c36`.

## 2026-08-08: fuse the T1 return into T2 setup

The specialized BSIG1 helper now jumps to PC 714 instead of the end of the old
T1 landing pad. From there, one packed fall-through path loads `h0`, the mask,
`h2`, and `h1`, then enters `Maj`. Twelve unreachable `PUSH1 0` instructions
and five `STOP`s preserve the original 56-byte, 30-instruction region and all
downstream boundaries. The semantic endpoints for `afterT1`, `gotT2H2`,
`gotT2H1`, and the `Maj` entry remain unchanged apart from their earlier PCs.

Native scoring accepted all 38 clean/dirty runs at **3,498,907** with identical
paired gas; the empty vector costs **55,087**. The exact improvement is 14 gas
per round, 896 per padded block, and 58,240 across the 65-block suite. The
full execution, correctness, composition, and exact-gas builds pass with 1,499
fixed gas and 53,296 gas per block. The exact bytecode SHA-256 is
`ce4f458a442d8f7eb7976d3439040b3c926ded1d10d5653f9abfb82558ebbe6e`.

## 2026-08-09: integrated T1/T2 kernels

The standalone Ch/BSIG1 and Maj/BSIG0 continuations were collapsed into two
caller-specific straight-line kernels. T1 now consumes e/f/g, computes Ch and
the chained BSIG1, adds K[j], W[j], and h7, masks once, and lands at the
existing after-T1 boundary. T2 similarly combines Maj with chained BSIG0 and
lands at the existing after-T2 boundary. Dead helper bodies and the first
forwarding trampoline supplied the structural-instruction reservoir, so the
artifact remained 1,524 bytes and 810 instructions.

The trusted scorer and full Yukon run agreed on **3,186,907**, with empty gas
**50,287**, all 19 clean vectors passing, all dirty-frame runs matching, Lean's
default kernel accepting the proof, and Comparator accepting the candidate.
Submission `a74ec96d-8be3-41f2-a719-d3efdd8952fa` was promoted. Exact bytecode
SHA-256: `379be39507d9b236e894102a5abd356c034c7d6d45926959fcc57446c0f4e2f6`.

Process lesson: freeze a scorer-passing byte sequence before proof work, make
the new helper end at an existing semantic state, and regenerate the complete
instruction/PC artifact first. This kept the difficult change localized even
though the helper ABIs changed substantially.

## 2026-08-09: global structural balancing and direct output

The next pass treated unreachable byte ranges as a global structural budget.
Live sequential `JUMPDEST` padding in the schedule, state updates, round tail,
feed-forward, padding loop, and outer driver increment was removed by widening
immediates without changing their values. The displaced instruction count was
moved into unreachable forwarding trampolines, dead accessors, and helper
padding. All eight terminal H accessor calls were replaced by fixed-address
MLOAD paths. Every live byte PC, the 1,524-byte length, and the 810-instruction
artifact remained fixed.

The candidate was killed and restarted twice during proof integration: first
when stale accessors remained imported by gas-only modules, and again when the
output gas proof still modeled the removed helper calls. The fix was to delete
unused accessor metering lemmas and meter the nine direct output blocks from
their located instruction lists. This produced an independently checked exact
model of **1,119 fixed gas plus 47,744 gas per padded block**, with compression
at 47,677, rounds at 486, schedule at 15,690, and output at 135.

Full `BENCHMARK_INSECURE_LOCAL=1 yukon run` passed the default kernel,
Comparator, and all 19 vectors at **3,130,807**; empty gas is **49,155**. The
exact bytecode SHA-256 is
`a01f9ca5dcb712b974fe4285161f957a9a394c19df26e1690bfb7fc8398a5630`.
Submission `bc160f88-434c-4013-ac73-2b37d9e54c1b` was queued with a 9 KiB
public note while the next architecture search began; validation is treated as
non-blocking.

Process evolution:

1. Native-score every byte candidate before any Lean edit and reject on the
   first clean/dirty mismatch.
2. Keep a promoted proof-complete checkpoint outside the workspace before a
   broad artifact rewrite.
3. Track gas as fixed, per-block, per-round, and per-invocation deltas; require
   all four views to reconcile before changing theorem constants.
4. Separate functional paths from gas-only modules so dead helper APIs can be
   removed rather than kept alive for obsolete proofs.
5. Treat Yukon validation latency as asynchronous: submit the last proved
   checkpoint, then immediately prototype the next candidate.

## 2026-08-09: ADHD architecture search after 3,130,807

Five isolated divergent frames (hardware engineer, speedrunner, remove the
load-bearing assumption, biology, and hostile competitor) generated 30 ideas.
Scores are novelty/viability/fit on a 0--10 scale. Ideas are grouped by the
underlying mechanism rather than by the frame that generated them.

### State-role renaming

- Circular memory register file with a three-bit phase `[N8 V8 F9]`
- Eight phase-specific fixed-address round entries `[N9 V6 F9]`
- Four modulo-renamed stack kernels `[N9 V5 F8]`
- Fully stack-resident A--H across 64 rounds `[N8 V4 F9]`
- Overlapping 60-byte H window with a rotating base `[N9 V5 F8]`
- Differentiating-cell logical identities over fixed slots `[N8 V8 F9]`
- Unaligned overlapping MSTORE update windows `[N9 V4 F7]`

### Schedule/operand streaming

- Interleave W expansion with compression in a 16-word ring `[N8 V8 F10]`
- Channel each new W directly into T1 before its ring store `[N8 V8 F10]`
- Sequential K+W operand cache in expired constant storage `[N8 V7 F8]`
- Lifetime-alias expired K, W, and feed-forward snapshots `[N7 V7 F7]`
- One unaligned MLOAD for paired W operands `[N8 V3 F5]`
- CODECOPY constants interleaved with continuation metadata `[N8 V5 F6]`

### Cross-round supersteps

- Two-round virtual midpoint with no intermediate materialization `[N8 V7 F9]`
- Pairwise round super-cycle forwarding T1/T2 `[N8 V7 F9]`
- Thread the finished T1/T2 accumulators into the next round `[N8 V6 F9]`
- Two-round polyprotein with one final cleavage boundary `[N8 V7 F9]`

### Packed or redundant representations

- Four guarded 256-bit lanes carrying paired H words `[N10 V3 F7]`
- Redundant duplicated 32-bit lanes for rotation-friendly sigma `[N8 V4 F6]`
- Pre-rotated state isoforms updated incrementally `[N9 V3 F6]`
- Packed counter/K/W/phase capsule advanced by one ADD `[N8 V6 F6]`
- Delay 32-bit normalization until observable boundaries `[N7 V7 F8]`

### Control-flow carries state

- W/K pointers replace the numeric round counter `[N7 V8 F8]`
- Descending K code pointer exits through unsigned underflow `[N8 V7 F7]`
- Multi-entry helper suffix selected by round phase `[N9 V5 F7]`
- Return-threaded continuation chain encodes next K/W address `[N9 V4 F7]`
- Eight residue-class continuations hardwire H rotation `[N9 V6 F9]`

### Input/finalization fusion

- Process full blocks from calldata and materialize only terminal padding `[N7 V7 F7]`
- Fuse feed-forward and digest packing into the final round exit `[N7 V9 F7]`
- Reuse the final paired-round body to perform feed-forward immediately `[N7 V8 F7]`

The weighted shortlist (0.35 novelty, 0.40 viability, 0.25 fit) is:

1. **Streaming 16-word W ring** -- highest direct fit and removes the separate
   15,690-gas schedule phase while reusing the current recurrence arithmetic.
2. **Rotating physical H roles** -- potentially removes most of the 142-gas
   update phase, but only if phase is carried by control flow rather than a
   paid dynamic dispatch.
3. **Two-round virtual midpoint** -- halves loop control and may cancel first-
   round stores against second-round loads while preserving a two-step semantic
   specification.

The non-obvious viable pick is the rotating H role map: after 64 rounds the
phase returns to zero, so fold/output can retain their fixed-address boundary.
The immediate trap is code size: eight copies of the current round body cannot
fit, so the prototype must prove that only small address-specific continuations
need duplication.

Rejected traps:

- Guarded paired lanes: SHA rotations and 32-bit carries cross the guard
  structure often enough that unpack/repack cost is likely dominant.
- Pre-rotated isoforms: every new A/E value would require regenerating three
  rotations, moving rather than removing sigma work.
- Paired W MLOAD: recurrence dependencies are not adjacent, so one unaligned
  load cannot supply the required four words without a more expensive layout.
- Full return-threaded 64-round chain: code growth is incompatible with the
  current 1,524-byte artifact unless most arithmetic remains shared, restoring
  the jumps it was intended to remove.

Literature check:

- NIST FIPS 180-4 defines W[t] only from t-2, t-7, t-15, and t-16, validating
  the exact 16-word circular-window invariant.
- The IACR comparative SHA-2 hardware study explicitly evaluates factor-two
  unrolling, supporting the paired-round datapath but not proving it is cheaper
  under EVM gas.
- The Ethereum Yellow Paper gas schedule makes JUMP/JUMPI materially more
  expensive than PUSH/MLOAD/MSTORE and JUMPDEST, so phase specialization must
  use direct continuation geometry; a dynamic phase dispatcher is a trap.

Three temp-only prototypes were launched in parallel with hard kill criteria:
native clean/dirty correctness first, exact gas/byte accounting second, and no
Lean edits until a candidate beats 3,130,807 concretely.

### Prototype outcomes

The first streaming-schedule implementation was brought from two control-flow
faults to a full clean/dirty pass. It builds only W0--W15 before compression,
then computes W16--W63 on demand and carries the fresh word directly into T1.
Its exact score was **3,162,332**, a regression of **31,525** total or **485
gas per padded block**. The eliminated W reload did not repay the second phase
guard, dynamic backedge, and two extra continuation transfers. This version is
rejected. A future streaming design must remove at least 486 gas/block of
control rather than merely tightening the same geometry.

The rotating-state audit proved the physical-ring invariant and found an
optimistic ceiling of roughly 5,824 gas/block: only new A and new E need stores,
and the loop guard can be checked once per eight phases. It is not a local
splice. The integrated T1/T2 ABI must first accept phase-loaded H words while
keeping every selection within DUP16/SWAP16; the modeled fork does not activate
extended DUPN/SWAPN.

The two-round virtual-midpoint prototype is the first architectural win. It
loads A--H once, executes two rounds through dynamic helper continuations,
keeps the midpoint virtual on the stack, and materializes only the state after
the pair. All 38 clean/dirty rows passed. The artifact remains **1,524 bytes / 810
instructions**, reaches at most DUP12, and scored **2,970,647**: exactly
**160,160 below** the 3,130,807 checkpoint, or **2,464 gas per padded block**.
One pair costs 895 gas versus 972 for two materialized rounds. This candidate
advances to proof integration; the streaming candidate does not.

## 2026-08-09: two-round virtual midpoint — proof complete

The virtual-midpoint candidate is now the exact submission artifact. Its
bytecode SHA-256 is
`eb8c285b59def1ea1341d55c2d269a459ad0b808dffc4fccf7ff67dea72487f6`.
The bytecode remains 1,524 bytes and the generated structural artifact remains
810 instructions. No extended-stack opcodes are used: the deepest live access
is `DUP12`, so the trace stays within ordinary Osaka EVM instructions.

### Runtime design

The old compression body executed one complete round at a time. Each round
loaded the eight working variables, calculated T1 and T2, wrote all eight
logical values back to fixed memory slots, incremented the counter, and
repeated. Most of those stores merely materialized the state that the next
round immediately loaded again.

The new loop consumes two rounds per iteration. At byte PC 633 it checks the
even counter and loads the working tuple once. The first T1 and T2 return to
dynamic, statically certified continuation PCs. The resulting A1 and E1 stay
on the EVM stack alongside the original working words. The second round reads
its inputs from that virtual midpoint, computes A2 and E2, and only then
commits the eight canonical H slots. The back edge increments by two. After 32
pairs, counter 64 reaches the unchanged feed-forward loop at PC 935.

The two fused big-sigma kernels were generalized from fixed continuations to
valid dynamic return destinations. T1 now receives its two final addends from
the caller, so the pair body can provide `h + K[j]` and `W[j]` for each of the
two rounds without forcing an intermediate H-slot materialization. T2 uses the
same dynamic-return pattern. All four concrete continuation destinations are
proved valid jump destinations in the frozen bytecode.

One pair costs exactly 895 gas. Two old rounds cost 972 gas, so the pair saves
77 gas. There are 32 pairs per padded block, yielding the measured 2,464-gas
per-block improvement. The public suite contains 65 padded blocks, hence the
exact suite improvement is `2,464 * 65 = 160,160` gas. This takes the promoted
3,130,807 checkpoint to 2,970,647. Empty-input gas is 46,691.

### Proof architecture

The proof was rebuilt from the frozen raw bytes upward rather than transported
from native test vectors. `Bytes.lean` is reducible to the exact candidate
hex, and `Artifact.lean` contains the complete 810-entry decoded instruction
array with byte PCs and well-formedness certificates. The pair executor is
split into small located blocks: condition, first T1 setup, first T2 setup,
second T1 setup, second T2 setup, and commit/backedge. Each block has a direct
small-step theorem, and their `GasSteps` witnesses compose into one pair and
then 32 bounded iterations.

The functional layer defines the usual eight-word SHA-256 `Working` record and
one pure mathematical round. It proves the first virtual A/E values equal one
round of that function, then proves the second virtual A/E values equal a
second round. The commit theorem writes A2, A1, A, B, E2, E1, E, and F to the
canonical slots and proves those eight words represent precisely two pure
rounds. A 32-pair induction therefore represents 64 standard SHA-256 rounds,
not a new or weakened specification.

The invariant also proves that every pair preserves the packed K table, the
64-word schedule, the saved pre-round chaining state, calldata-derived padded
blocks outside scratch memory, the execution environment, halt state, and
call stack. This reconnects at the existing feed-forward proof, which adds the
saved chaining words and reaches the existing outer driver and digest-output
theorems. The final theorem still establishes `Challenge.Sha256.Correct` for
every calldata value; clean and dirty vectors are only falsification checks.

A clean-source audit exposed stale single-round modules that cached object
files had initially hidden. Those layers were replaced with the 32-pair
executor and pair-preservation lemmas before the official run. The benchmark
artifact was then regenerated from the exact current hex, preventing a proof
from accidentally targeting an older candidate.

### Verification record

The exact official command was:

```text
BENCHMARK_INSECURE_LOCAL=1 yukon run
```

The insecure-local flag is required by the benchmark harness on Darwin; it
does not weaken the Lean theorem or native vectors, but uses Comparator's local
fake sandbox instead of ranked landrun isolation. The resulting gate reported:

| Check | Result |
|---|---:|
| Lean submission build | accepted |
| Lean default kernel | accepted |
| Comparator | accepted |
| Clean correctness vectors | 19/19 |
| Dirty-frame native runs | all matched clean gas/results |
| Bytecode size | 1,524 bytes |
| Structural instructions | 810 |
| Verified score | **2,970,647** |

No `native_decide` or new trusted axiom is used in the exported proof. The
accepted proof relies on the benchmark's allowed kernel foundations
(`propext`, `Quot.sound`, and `Classical.choice`) and ordinary reducible
arithmetic/list operations.

### Course corrections and next work

The main proof-engineering failure was asking Lean to reduce the complete
post-pair state definitionally when proving frame fields. That triggered
multi-minute heartbeat exhaustion. Small generic lemmas showing that loads,
stores, and helper returns preserve `executionEnv`, `halt`, and `callStack`
made the 32-pair composition compile reliably. Likewise, the eight final H
writes were proved through named intermediate states instead of one enormous
normalization.

The streaming schedule prototype was retained in this ledger as a negative
result because it looked architecturally stronger but regressed by 485 gas per
block. The pair design won because it removes intermediate state traffic while
keeping the full schedule and fixed feed-forward boundary unchanged.

Promising next steps are a four-round superstep or phase-rotated physical H
slots, provided the resulting stack layout stays within `DUP16`/`SWAP16` and
does not reintroduce dynamic-dispatch gas. Any follow-up should begin from this
proof-complete 2,970,647 checkpoint, native-score clean and dirty states first,
and only then extend the pair invariant.

Development context: GPT 5.6 Sol, xhigh effort, Codex agent.
