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
