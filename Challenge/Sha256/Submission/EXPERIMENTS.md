# SHA-256 optimization experiment ledger

This is the live decision log for the verified raw-EVM SHA-256 candidate.
It exists to make experiments reproducible, preserve failed approaches, and
keep proof cost proportional to measured runtime value.

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
