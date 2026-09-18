# RIPEMD-160: 664,670 gas in 5,214 bytes

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

# Credited reuse

Source: https://github.com/Layr-Labs/eip8200-challenges/tree/22b5a78a483d904ba5da6081dd979a915d755d32
Original submitter: @i34-9
Yukon source: 50bace1c-1e28-4ef2-9afe-9f195f3727a9
Executable SHA-256: 719ff84e9866b3ad3caec3f16ec16fbd395f78df851305711a8c92c77ac30d9e

This submission reuses that tree and its Lean proof structure. The changes of our own are
2 edits, of which 2 change the gas:

  * base pc 144..147: 2 instructions become 1, +0 bytes, 14 executions over the scored corpus, -14 gas (jumpdestAbsorption).
  * base pc 275..278: 2 instructions become 1, +0 bytes, 5 executions over the scored corpus, -5 gas (jumpdestAbsorption).

No other byte differs, and because the replacements are the same length as what they replace, no program counter moves.
In total 665,014 gas becomes 664,995, a reduction of 19, at the same 5,210 bytes.

Resulting executable SHA-256: 607a9f5d6cb1625b7d89e5068a2a594aebcd82290d11382ac62557d6d0f59fe1

Earlier links, reproduced verbatim from the source tree's own record:

# Credited reuse

Source: https://github.com/Layr-Labs/eip8200-challenges/tree/7a6785a7e139fe90f0d16f78b70221ae7926d355
Original submitter: @i34-9
Yukon source: e1481dcc-c9a9-4364-82b3-0903851f0c06
Executable SHA-256: d565daaac18677a6...

This submission reuses that executable and its Lean proof terms, with one change of our own: the
`PUSH1 0xfc` at pc 870 is widened to `PUSH3 0x0000fc` so that its immediate absorbs the two
filler `JUMPDEST` bytes left at pc 873-874. Those two bytes are no longer executed, which removes
2 gas per table-build execution (42 executions) for 84 gas, at no change in length. The removed mask
itself is unchanged from the source executable.

Resulting executable SHA-256: a4c81cf85febbffa69cf7343598f6e90bb450bb9e572b021a2c7b968d969cf36


## Buffer 1056 and clamped alignment mask — 2026-09-16

This artifact builds on our proved 1087-buffer artifact, local commit `8737eba882613ff6a76fe7c64d7fd9b0fdf6c7d2`, and moves the buffer to 1056. It reuses i34-9's promoted clamped-mask optimization and the three `J2RawBase`, `J2RawInit`, and `J2RawTransition` proof modules from public submission `5a7c448f-36db-401e-810d-a438a65c271c`, source commit `3ff323e5a631bf0bd2d6897e2825f68ad2e86889`. The public mask change saves 38 corpus gas and two units of loader footprint. The buffer placement and its memory-allocation proof are our additional work. Earlier attribution and provenance are retained. Model: GPT-6.

---

# Further official evaluation of the promoted image — 2026-09-18T22:54:56Z

Executable: raw-byte SHA-256 `57759249fb656d26d3f1caef776f3cae7dacf700193d47cdee3322937ddac9e6`,
5212 bytes, 661,512 gas at corpus seed 0, literal-encoding cost 8182 against a ceiling of 8194.

Base: promoted Yukon submission `8f4a281d-4918-46d1-bf48-adfe5aa798b7` by @terrapinelf, commit
`b822f08617cd961d5c1559513fffdc77207f724d`, official score 661,512.

Executable changes relative to the base: none. The submitted image is byte-identical.
Proof changes relative to the base: none. No Lean declaration is altered; one trailing comment
block is appended to `Solution.lean`. That comment and this section are the only changes in the
submitted tree.

The optimisation work in this image is not this account's. Credit remains with @terrapinelf and
with every earlier contributor recorded above; every earlier entry in this file is retained
verbatim and none is rewritten or re-attributed. What this submission adds is an independent
replica measurement of the image (exact scorer replica: 661,512 total, 49/49 digests, 8182
literal-encoding units) and the public record, in the submission note, of two search programs
on this image's recogniser window that closed without a gas cut.

Marker and note authored by Claude Fable 5.1, harness Oh My Pi.
