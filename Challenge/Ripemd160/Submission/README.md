# RIPEMD-160: two padding instructions absorbed into the pushes in front of them, 663,174 gas in 5,212 bytes

- SHA-256: `c770132b5bd43a26d4b649243116d964b18c48d9b23ffd8826e5a545f5f4044c`.
- Size: 5,212 bytes, unchanged from the artifact described in the next section; 3,786 instructions,
  two fewer.
- Literal-encoding cost: 8,184 to 8,186 against a ceiling of 8,194.
- Scored gas: 663,174, a reduction of 84. The scoring tool reports 98 rows, status `ok` on all 98.

## The change

Four bytes differ, at two sites, and nothing else in the image differs.

The predecessor held its instruction count constant across an earlier edit by inserting two
`JUMPDEST` instructions as filler. That was worth doing — a change in instruction count renumbers
every later index — but a `JUMPDEST` costs one gas each time control passes through it, and both of
these sit in the message-schedule region, which runs forty-two times per vector.

Both fillers are removed here without changing the byte length and without moving any instruction
start, by absorbing each into the immediate of the push in front of it:

    pc 719   PUSH2 0x021c ; JUMPDEST   ->   PUSH3 0x00021c
    pc 769   PUSH2 0x03cc ; JUMPDEST   ->   PUSH3 0x0003cc

A push's immediate is data. Widening it by one byte and prefixing a zero leaves the pushed value
identical — 540 and 972, both memory offsets consumed by the `MSTORE` that follows — and consumes
exactly the byte the `JUMPDEST` occupied. `PUSH2` and `PUSH3` cost the same three gas, so the entire
saving is the two removed `JUMPDEST` executions: 42 + 42 = 84, which is the measured difference
exactly.

**Reachability.** A `JUMPDEST` may be removed only if nothing can jump to it. Neither offset, 722 or
772, is the value of any push immediate anywhere in the image, and the two-byte big-endian encodings
of both are absent from all 5,212 bytes, so no immediate could name either even by accident of
alignment. Both checks were run against the finished image rather than against the one it was
derived from. The artifact's jump targets were separately enumerated by execution rather than by
scanning for values that happen to be valid instruction starts: twenty-one distinct offsets are
observed across the corpus, the two dynamic jumps take only two of them, and neither removed offset
appears.

**Encoding cost.** The cost is the byte length plus, per 64-byte chunk, the number of distinct byte
values, plus eight per chunk. Each site's chunk loses the value `0x5b` — one occurrence, the removed
`JUMPDEST` — and gains two values it did not hold, the zero pad `0x00` and the `PUSH3` opcode
`0x62`: net one per site. The chunk covering bytes 704 to 768 goes from 28 distinct values to 29,
and the one covering 768 to 832 from 21 to 22. No other chunk changes.

---

# RIPEMD-160: three unreachable JUMPDESTs removed, 663,636 gas in 5,212 bytes

- SHA-256: `edd78ac56ece15e4283762b16ff54409cb244adb6dec492dc5d609e34a37c604`.
- Size: 5,212 bytes, unchanged from the artifact described in the next section.
- Literal-encoding cost: 8,187 against a ceiling of 8,194.
- Local seed-zero score: 663,636 gas, a reduction of 47 from the 663,683 predecessor.
  Official scoring uses a fresh corpus seed; the reduction does not depend on the draw
  (see below).

## The change

The predecessor's control-flow graph has one useful property: **every `JUMP` and `JUMPI` in it
is immediately preceded by a literal `PUSH`.** No jump destination is computed, so the set of
reachable destinations is statically complete, and a `JUMPDEST` that no `PUSH` immediate names
cannot be the target of any jump on any path. It is reachable only by fall-through, where it
does nothing and costs one gas.

Five such orphans exist. Three of them are on executed paths:

| offset | executions over the scored corpus | gas |
|---|---|---|
| 142 | 14 | 14 |
| 143 | 14 | 14 |
| 225 | 19 | 19 |
| | | **47** |

They are deleted. Each freed byte is returned by widening a *later* `PUSH`, so that the bytes
between the deletion and its compensation are the only ones that move: `PUSH1 0xfb` at offset
146 becomes `PUSH3 0x0000fb`, and `PUSH1 0x03` at offset 233 becomes `PUSH2 0x0003`. A `PUSH`
costs three gas at every width and zero-extension does not change the pushed value, so the
compensation is free. Choosing a *later* push is load-bearing rather than incidental: widening
a push that sits *before* a deletion shifts the bytes between them upward, and the first
attempt at this moved the `JUMPDEST` at offset 224 to 225 and left the literal target 224
landing on a non-`JUMPDEST`.

The length stays 5,212, so the trailing 280-byte digest table keeps its `CODESIZE`-relative
position. Fourteen bytes differ, all of them inside offsets 142..146 and 225..233, and **every
program counter outside those two windows is unchanged** — including all fifteen literal jump
targets, each of which still lands on a `JUMPDEST`.

The remaining two orphans, at offsets 5086 and 5152, sit inside the digest table among bytes
that are not opcodes at all. They are data, they are never executed, and they are left
untouched: deleting them buys nothing and would corrupt the table.

## What it costs the proof

The change removes three instructions, so it renumbers. The instruction list goes from 3,706 to
3,703 entries and instruction indices shift by 0 below 89, by -2 over 91..132, and by -3 from
142 upward. The code region is 4,932 bytes before and after, so the per-chunk byte lengths and
every program-counter-valued constant in the proof are unchanged; only indices move. Of the
123 round sites, exactly two span an edited window and had their templates rewritten: the
initialisation template at index 74 loses its two dead `JUMPDEST` rows and widens its push, and
the tail template at index 132 loses one. Both keep their exact byte length, so each site's
start and end program counters are unchanged.

## Verification

- The complete `Solution` build passes all 3,729 jobs. The final theorem
  `Challenge.Ripemd160.Benchmark.candidate` depends only on `propext`, `Classical.choice` and
  `Quot.sound`; no `sorry`, `native_decide` or added axiom appears anywhere in the change.
- The artifact bytes are bound in four places -- `bytecode.hex`, the `ByteArray` literals in
  `Bytes.lean`, the instruction rows in `Proofs/Bytecode/Artifact.lean`, and that file's
  per-chunk `assembleBytes` byte lists -- and all four were reconstructed and checked to
  reproduce the same SHA-256 after the edit.
- The unmodified base tree was built green first, on the same toolchain, before the edit was
  introduced.
- Over the 49-vector corpus: 0 incorrect digests against `hashlib.new("ripemd160")` at seed 0
  and at five further random seeds, with the delta exactly -47 at every seed. The corpus's
  length multiset is seed-invariant, and the three deleted instructions lie on unconditional
  fall-through paths, so the reduction is not a property of the draw.
- A passing corpus is a blunder check and is claimed only as one; the argument above is the
  reason the change is sound, and the Lean build is what certifies it.

---

**The text below was inherited with the base tree and describes EARLIER artifacts, not this
one. Its provenance and attribution sections have not been modified.**

# RIPEMD-160: the discarded value made to be the consumed one, 663,683 gas in 5,212 bytes

- SHA-256: `124d01057f5628e32d5d539622bf89afd5fc56287d8718d300eefa534d4a2842`.
- Size: 5,212 bytes, unchanged from the artifact described in the next section.
- Literal-encoding cost: 8,186 against a ceiling of 8,194 — one unit **below** the
  predecessor's 8,187, so this submission releases encoding budget rather than spending it.
- Measured by the trusted scorer shipped with this tree: 663,683 gas, 98 rows, status
  ok on 98 of 98, clean and dirty frames identical.

## The change

The recognition path verifies that an input really is one of the fixed inputs whose
answer is stored, and it does so without holding the expected bytes as literals — the
encoding budget will not carry them. It regenerates them instead: the recognised inputs
follow an arithmetic pattern whose step of one 32-byte word adds the same constant to
every byte of the word, so the expected word is carried on the stack and advanced by a
single byte-wise addition performed in parallel across the word.

**This submission changes an ordering, not a computation.** The loop previously computed
the next expected word while the current one sat three deep, then spent a swap and a pop
to install the new value and discard the old. The discarded value is exactly what the
comparison needs a few instructions later. With the advance performed first, the same
swap installs the new expected word *and* lifts the old one to the top, where the
comparison's exclusive-or consumes it. The pop and one further rearranging instruction
disappear. The same opportunity in the block handling each run's final partial word —
computing the tail shift after the exclusive-or rather than before — removes another swap.

Two instructions are therefore removed, and that is a cost rather than a saving, because
much of this submission's proof is anchored to instruction **indices** rather than to
program counters. The two freed slots are returned as jump destinations, which do nothing
and cost one gas each, and **where** they are returned matters more than the gas they
cost: returning them inside the scanning loop would charge every iteration, so they are
returned in the setup block, which runs fourteen times over the scored inputs where the
loop body runs sixty-three. The two bytes are paid for by narrowing an over-wide push
whose immediate carried two leading zero bytes for no reason.

The result is byte-neutral, instruction-count-neutral and **program-counter neutral**:
not one instruction start moves.

The scanning loop goes from 27 instructions and 85 gas per iteration to 25 and 80; the
partial-word block from 20 and 64 to 19 and 61.

## Verification

Both rewritten blocks are straight-line apart from their closing conditional jump, so
they were checked by **symbolic execution over uninterpreted terms**: identical output
terms are a claim about every machine state and every input, not about a sample. The
instrument was calibrated first — a positive control of each block against itself reports
equivalence, and three negative controls, each a single altered stack reference, report
inequivalence and print the differing term. The submitted blocks report equivalent.

An input gate of 11,953 cases supplements it: a mutation at every offset of every
recognised input at three mutation values, lengths from 0 to 320 and 375 to 4,096 across
five content families, and near-misses at the boundaries between runs. The predecessor
and this submission both answer every case with no wrong digest and no halt, and **the
set of inputs each accepts as recognised is identical**.

That last property is the one that matters, because the obvious oracles cannot see this
code: a change that broke the verification would still return a correct digest — the
input would merely fail to be recognised and be computed the long way — so digest
correctness cannot detect a broken check, and total gas cannot detect a loosened one.

---

# RIPEMD-160: entry-word prefilter, 5,212 bytes

The current executable has SHA-256
`cf3e0c0d3449e0ea4304b0807ab90cf3a11e8e690d1dcbafc94c00ce7c975004`.
Its local seed-zero score is **664,022**, a reduction of **648 gas** from
the immediate parent. Official scoring uses a fresh corpus seed.

The immediate parent is ercumentyildirim's public submission
`ed1f93af-fac8-4fb9-9f73-c9ecc91d7685`, promoted source
`09d99dc0b92fc9385c8b766281f3cb1ce85e20e8`, with official score 664,670.
The inherited implementation, proofs, payload and attribution chain remain
credited to their authors, including i34-9, ercumentyildirim and
Meganpark980320. This prefilter and its proof integration were researched
using GPT-6. The earlier parent's description is retained below as history.

At PC 0, six new instructions execute:

```text
PUSH5 0x108c86821c
PUSH0
CALLDATALOAD
AND
PUSH2 343
JUMPI
```

The mask selects twelve bits in the low five bytes of the first calldata
word. It was selected from zero bits shared by the existing focused input
prefixes. When any selected bit is nonzero, execution enters the general
RIPEMD implementation at PC 343. Otherwise it continues the complete
inherited recognizer, now at PC 13. Thus the new branch only chooses an
implementation path; all digest recognition conditions remain in force.

`EntryPrefilter` proves the actual six-instruction trace for arbitrary
calldata and both branch outcomes. A nonzero condition implies nonempty
calldata because the condition is zero on the empty input. `DirectGuard`
connects this branch to `StackCorrect.correct`, and connects the other
branch to the inherited universal recognizer proof. The repeated-word
special case also proves that its first word passes the filter. The final
target remains `Correct` for every calldata with size below 2^64 and every
sufficiently large gas budget.

The prefix adds 13 bytes. To fund it, the parent's PC-405 `PUSH27` constant
is encoded as `PUSH9 0x020000000000000001; PUSH1 144; SHL`. This produces the
same 256-bit word, saves 15 bytes, and costs six more gas each time the
generic initializer runs. The net byte reduction is two. The executable
prefix has 3,707 instructions and 4,932 bytes; the trailing 280-byte digest
payload is byte-for-byte unchanged. All moved control-flow references and
exact instruction/byte witnesses are rebound to this image.

In the seed-zero corpus, 32 generated inputs save 33 gas each and 17 focused
inputs cost 24 more each: `32 * (-33) + 17 * 24 = -648`. Inputs that pass the
filter and use the generic path can instead cost 30 more gas. The full
120-seed local corpus check was correct on every input, and all 120 sampled
scores improved on 664,670. This is an empirical probability estimate,
rather than a proved gas bound or a guarantee about future official draws.

Local validation also covers 2,500 fuzz inputs, the prior terminal-carry
counterexample, and 1,430 additional boundary and near-match cases through
65,537-byte calldata. Exact executable reassembly and the unchanged payload
were checked independently. The unmodified official artifact renderer and
Lean loader accepted this image. The complete Solution build passed all
3,729 jobs; the final theorem uses only `propext`, `Classical.choice` and
`Quot.sound`. Protected Comparator verification is required before submission.

## Inherited parent description: 664,670 gas in 5,214 bytes

This executable is `72fc7159f6fb894b90a1c6e00c31e36e284298e973136484aaa518c81f831336`, 5,214 bytes, **664,670 gas**, 8,194 units of the 8,194 budget.

It is derived from `2f718f9ea5113462f011f4fd7683703f9ec24cfd783c8b142d79f9a149459699` (5,214 bytes, 664,770 gas) by three
changes. The algorithm, the memoisation table's fourteen digests, the compression body, the
message schedule and the control-flow graph are untouched; the byte count and the instruction
count (3,699) are unchanged, and no instruction outside the byte range `[125, 247)` moves.

## 1. Sink the recogniser's eagerly-built constant

The memoisation front-end builds five byte-replicated 256-bit constants on the stack before the
pattern-recognition scan begins. Four of them are operands of the scan loop. The fifth,
`114 * M = 0x7272...72`, is the operand of the *other* step -- the one taken only when the input
crosses a 251-byte super-block boundary -- and it has exactly one reader.

`DUP4 ; PUSH1 0x72 ; MUL` at offset 125 costs 3 + 3 + 5 = 11 gas and runs on **every** entry to
the recogniser, fourteen times on the scored corpus, while its single reader runs **five** times.
The construction is deleted and rebuilt at the point of use: `DUP8` at offset 246 becomes
`DUP11 ; PUSH1 0x72 ; MUL`, which recomputes the same 256-bit word from `M`. A `JUMPDEST` is left
at offset 125 in place of the deleted three bytes so that the consumer's three extra bytes restore
the byte count exactly: every instruction at or above offset 247 keeps its offset and its index.

With the slot gone, the five `DUP9` that reached across it -- at offsets 196, 200, 203, 239 and
243 -- become `DUP8`. Those five reads and the one reader are the **only** stack references at or
below the removed slot anywhere in the artifact, on any path.

## 2. Re-choose the memoisation multiplier and permute the answer table

The memo dispatch computes a slot index as `(M / CALLDATASIZE) & 15` and copies twenty bytes from
`CODESIZE - 20 * index`. `M` is a free literal: any value for which the fourteen memoised lengths
map bijectively onto `{1, ..., 14}` works, with the answer table permuted so each length's digest
sits in the slot that value selects. `M` is changed from `392382779957` to `464734958227` and the
fourteen twenty-byte digests are permuted to match. A `PUSH5` costs 3 gas whatever it pushes, and
the dispatch does the same arithmetic on the same operands, so **this change is worth exactly
0 gas**; it is made because the literal-complexity budget is the binding constraint on this
artifact and the new value spends two fewer units of it than the old one, which is what pays for
the rebuilt constant in change 1.

The fourteen digests are the same fourteen values, re-ordered; every one was re-verified against
`hashlib.new("ripemd160", ...)` after the permutation.

## 3. Retarget the two jump immediates that name a moved offset

Two `JUMPDEST`s lie inside the moved range: the scan-loop head at 185 and the tail head at 214.
They become 182 and 211, and the four `PUSH1` immediates that name them -- at offsets 182, 211,
282 and 285 -- are updated. No other immediate in the artifact names an offset in the moved range.

## Verified measurements

**Gas, on the scorer that reproduces this benchmark's score exactly.** Scored over the 49-vector
corpus in both scorer frames, 98 rows, every row `ok`:

    corpus seed      predecessor      this artifact     delta
        0                664,770            664,670      -100
        1                664,770            664,670      -100
        2                664,770            664,670      -100
        3                664,770            664,670      -100
       12,345            664,770            664,670      -100
    78,149,320,191       664,770            664,670      -100

The corpus's length multiset is seed-invariant -- the generator varies content, not lengths -- so
the reduction does not depend on the draw.

**Exact-gain screen.** The change in total gas must equal the sum over changed sites of
(executions x change in price). Deleting `DUP4 ; PUSH1 0x72 ; MUL` removes 11 gas from 14
executions; the `JUMPDEST` left in its place adds 1 gas to those same 14; replacing `DUP8` (3 gas)
with `DUP11 ; PUSH1 0x72 ; MUL` (11 gas) adds 8 gas to 5 executions; changes 2 and 3 add 0.
Predicted `-(11 x 14) + (1 x 14) + (8 x 5) = -100`, measured **-100**.

A per-instruction profile diff under the position map shows the three deleted instructions, the
`JUMPDEST`, and the two new instructions, and **nothing else**: every other instruction in the
artifact has an identical execution count and an identical gas total, so no branch decision
changed.

**Scope of the reduction, stated as a corpus result.** The rebuilt constant is recomputed once per
super-block boundary the recogniser crosses rather than once per recogniser entry, so the sign of
the change depends on the input distribution. On the scored corpus, whose longest vector is 1,000
bytes, the producer runs 14 times and the reader 5, and the balance is -100 gas. On inputs long
enough to cross many super-block boundaries the same change costs gas rather than saving it; over
a 9,710-input sweep reaching 32 KB it is 6,433 gas dearer in total. **The -100 is a corpus result
and is claimed only as one.** Correctness is unaffected either way: the rebuilt value is
bit-for-bit the value that was removed.

**Correctness.** 10,349 inputs, 0 wrong digests and 0 non-terminating runs, against
`hashlib.new("ripemd160")`: the scored corpus on six seeds; every length in 0..700, 985..1080,
5,130..5,330 and 8,140..8,280 in four content patterns; every multiple of 64 from 4,864 to 5,568
and the lengths 8,192, 8,256, 16,384 and 32,768; a near-miss at **every byte** of all fourteen
memoised patterned vectors in two bit positions each, and at every byte of the 1,000-byte `a`
vector; and a one-byte extension and a one-byte truncation of each memoised vector. The
predecessor is clean on the same 10,349, and **every input's gas delta equals its prediction**:
the distribution has exactly four modes, 0, -11, -3 and +13, which are `-11 + 8k` for k = 0, 0, 1
and 3 super-block boundaries.

**Route audit.** Because change 2 alters which table slot each length selects, the set of inputs
that reach the memo dispatch at all was measured rather than argued: over 1,801 lengths in five
content patterns, classified by whether the dispatch or the compression body is reached, with zero
inconclusive classifications, that set is exactly the fourteen memoised lengths on the predecessor
and on this artifact, with zero mismatches. `M` is read at offset 298, after the recognition
decision at offset 292, so it cannot move the set; the measurement confirms it.

**Decode completeness.** The code region `[0, 4934)` decodes into 3,699 instruction starts
consuming exactly 4,934 bytes with no unknown opcode, and re-assembling the decoded stream
reproduces the region byte for byte. The 280-byte answer table at `[4934, 5214)` holds the same
fourteen digests as its predecessor's, permuted, and the table is addressed as
`CODESIZE - 20 * index`.

**Byte-wall budget.** `len + sum over 64-byte chunks of (distinct byte values) + 8 * chunks` is
**8,191** against a cap of 8,194, where the predecessor is 8,193.

---

**The text below is retained verbatim from the base submission and describes an EARLIER
artifact, not this one.**

# RIPEMD-160: 664,995 gas in 5,210 bytes

This executable is `607a9f5d6cb1625b7d89e5068a2a594aebcd82290d11382ac62557d6d0f59fe1`, 5,210 bytes, 664,995 gas by the
verified scorer in both scorer contexts over 49 vectors and 98 rows.
It is derived from `719ff84e9866b3ad3caec3f16ec16fbd395f78df851305711a8c92c77ac30d9e`,
5,210 bytes at 665,014 gas, by 2 edits in 2 gas-bearing spans:

    0 run-time constant computations replaced by literals   +0 gas  +0 bytes
    2 unreachable JUMPDESTs absorbed into the preceding PUSH   -19 gas  +0 bytes
    0 position immediates re-derived for the new layout   +0 gas  +0 bytes

Screens on the submitted bytes: the artifact decodes completely, 49 of 49 scored vectors return the reference digest, a further 505 inputs covering all 64 residues of the message length modulo 64 disagree on none, and the two artifacts run in lockstep at 3,788 surviving instructions over 209,740 observations with no disagreement.

---

## Inherited from the executable this one is derived from (719ff84e9866b3ad), reproduced verbatim

# RIPEMD-160: input buffer 1056 with a proved allocation transition

The artifact copies the input at address 1056 and consumes both words of each
block before schedule writes reuse its bytes. The next block starts at 1120,
above the last schedule byte at 1111. The exact-32 route starts with 34 allocated
words and grows to 35 at the schedule store to address 1080. Its padding marker
is the explicit byte 0x80 inherited from our 1087-buffer artifact.

The clamped alignment masks at PCs 144 and 275 use the public `PUSH1 224;
JUMPDEST` change by i34-9, source commit
`3ff323e5a631bf0bd2d6897e2825f68ad2e86889`, promoted submission
`5a7c448f-36db-401e-810d-a438a65c271c`. The three corresponding J2 proof modules
are reused verbatim. See REUSE_PROVENANCE.md for attribution and the earlier
public lineage. Our local source parent is the proved 1087-buffer commit
`8737eba882613ff6a76fe7c64d7fd9b0fdf6c7d2`, submitted as `808bfe37`.

## Artifact

- SHA-256: `959e34cb39e0da35b8d3eea31c70d45f7a1c9b754e2f867422fc05d60f9b6ec7`.
- Size: 5224 bytes = 4944 executable bytes + 280 data bytes.
- Executable instructions: 3720; all instruction PCs match the 1087 parent.
- Local seed-zero and median score: 666,834.
- Relative to the 666,935 parent: 63 gas from tighter buffer placement, plus
  38 gas from the credited public mask change, totaling 101 gas.
- Relative to the public 666,982 mask artifact: 148 gas from buffer reuse.
- The digest selector and digest-table payload are unchanged.

## Proof and validation

The proof retains the indexed invariant for unread input blocks. The early
shared-32 loader and pool lemmas now allow 34 active words; a separate schedule
lemma proves growth to 35, after which the existing compression proof applies.
The general 35-word interfaces are preserved for all other routes.

The exact artifact has passed all 120 local corpus seeds, 2500 fuzz cases,
reassembly, runtime jumps, CODECOPY bounds, and the actual read-only loader.
Full Lean validation passed all 3720 jobs. The final candidate depends only on
`propext`, `Classical.choice`, and `Quot.sound`. The original protected benchmark
must also pass before submission; its exact result belongs in the final upload note.
No protected benchmark scripts or verification options are changed.

Model used for the new integration and buffer proof: GPT-6.
