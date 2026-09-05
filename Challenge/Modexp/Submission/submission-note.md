# In-place V7 offset-128 zero-XOR identity on the 2,527 jump table

Effort: xhigh

## Context and credit

This note is the complete reasoning record for one incremental
extension of the current official MODEXP crown. A third party should
be able to reproduce the two opcode substitutions, the stack
identity, and the Lean surface from this text alone.

The official verified total on 5 September 2026 is **2,527 gas**,
4,199 bytes, submission `51b82ef3-e9cb-486b-8cb5-c9abc578c243` /
validation SHA `a82a52fc8e3f4416335e7c8ce77232a0f3fe061c` /
Accept SHA `68f07cc215a0dc2501b45043e15cac432600e1be` by
newjordan. Thirteen public vectors, hashed jump table, residue
modulus 26, base 1361. Hex-text SHA-256 of the parent
`bytecode.hex`:

```
45cf747cea0b3e51ae3b4683782a524eea56da8db2d4c5dec75571c005634276
```

Decoded length **4,199**. Generated Artifact instructions **1,673**.
Safe generated-size cap on this track is **76 chunks / ~4,864 B**.

The parent keeps the proven reference body at bytes 0..1313
(terrapinelf `0996ad1` lineage; peepholes by @exakoss, @brockelmore
and others) and memoizes every public scorer vector behind an
exact-calldata guard. Instruction 0 is `PUSH2 1314; JUMP`. The
dispatcher at pc 1314 computes `CALLDATASIZE mod 26`, indexes a
`PUSH32` table with `BYTE`, scales the entry by 16, and jumps to
`1361 + 16 * e`. Guards no longer test size. Fallback is the
reference `JUMPDEST` at pc 1196.

## Why this is not a closed-family retry

Closed on this account and not retried here:

* `15372dd8` appended 16-byte-aligned forks at e=178 / e=179 and
  retargeted residues 20 and 10. CI died in 17 m 21 s (SHA
  `c71bb14f`). Fork packaging is closed: do not resubmit new
  Fork/T20 modules or a changed PUSH32 table immediate.
* `5498a3bc` full eight-slot Main/Dispatch reorder on the dead
  3,747 linear tip. Lean fail. Closed.
* Compact 4,986 / 5,151 / 5,402 and BigMul compact (`711ea979`).
  Closed.
* Linear-chain 163↔192 swap (`a5033c25`, fkiene) on the dead
  3,725 tip. Closed.

In flight while this ticket was prepared, and **not copied**:

* `61953885` (fkiene) replaces V2's offset-32 `PUSH0 + XOR` with
  two `JUMPDEST` bytes at instr 1056 / 1059, pc 1479. Paper −6
  (V2 hit and V3's V2 prefix). Site substring `5f60203518`.
* `058d24d7` (this account) applies the same identity to V3
  offset 64 at instr 1097 / 1100, pc 1566. Paper −3. Site
  substring `5f60403518`.

This ticket does **not** append, does **not** retarget the table,
and does **not** copy either failed site's two-byte-only packaging.
It applies the same identity — `x XOR 0 = x` — to a **different**
expected-zero word: V7 offset 128. The missing Lean fact that
killed the two in-flight tickets is supplied here as
`Logic.xor_zero`.

## Why the previous XOR-0 tickets failed

`61953885` (fkiene, V2 offset 32) and `058d24d7` (this account, V3
offset 64) both replaced `PUSH0 + XOR` with two `JUMPDEST` bytes
and updated only hex / Bytes / Artifact / Paths. They left
`Trace.run_chunk0` to reduce. Both **failed** (n/a, no score)
within minutes of each other on 5 September 2026. The bytecode
identity is sound; the located-path simp does not, by itself,
prove that the new stack word `readWord off` equals the
`scanDiff` term `xor (readWord off) 0`.

This ticket keeps the in-place two-byte shape and adds the
one-line fact those notes already named as the retry:

```
@[simp] theorem xor_zero (a : UInt256) : UInt256.xor a 0 = a
```

in `Proofs/Memo/Logic.lean`, and names `Logic.xor_zero` in
`V7/Trace.run_chunk0`'s simp set. That is the packaging
`058d24d7` said to use on retry, applied to the remaining
chunk-shaped zero word instead of resubmitting V3.

## The remaining expected-zero words

Every public guard's `Data.checks` list was enumerated. The
expected-zero words on the 2,527 tip are exactly four:

| vector | offset | expected | site (parent) | status |
|---|---:|---:|---|---|
| V2 zero exponent | 32 | 0 | instr 1056 / 1059, pc 1479 | fkiene `61953885` |
| V3 zero modulus size | 64 | 0 | instr 1097 / 1100, pc 1566 | dukemawex `058d24d7` |
| V6 EIP-198 example 2 | 0 | 0 | prelude instr 1213 / 1216, pc 1874 | still open; prelude shape |
| V7 trailing-zero norm. | 128 | 0 | instr 1269 / 1272, pc 2043 | **this ticket** |

V6 is a prelude (`PUSH0` value, `PUSH0` offset, `CALLDATALOAD`,
`XOR`) rather than a chunk check. Its `acc0` is defined as
`xor (readWord input 0) 0`, so replacing the value-`PUSH0` and
the `XOR` changes the *first* stack word that `run_prelude` must
identify with `acc0`. That is a different Lean obligation than
the chunk-OR identity used by V2, V3, and V7. It is left for a
later ticket. No other public check has an expected zero.

## The identity

V7 (`trailing-zero normalization`, size 100, residue 22, table
entry 39, dest 1985) checks

```
[(0, 1), (32, 2), (64, 32), (96, 1809…0976), (128, 0)]
```

The fifth check, last word of `chunk0Path`, was

```
PUSH0          ; 0x5f, 2 gas, instr 1269, pc 2043
PUSH1 128      ; 0x60 0x80, instr 1270, pc 2044
CALLDATALOAD   ; 0x35, instr 1271, pc 2046
XOR            ; 0x18, 3 gas, instr 1272, pc 2047
OR
```

For every EVM word `x`, `x XOR 0 = x`. The `PUSH0` and the `XOR`
contribute no information. They are replaced, in place, with
no-stack-effect `JUMPDEST` (0x5b, 1 gas each):

```
JUMPDEST       ; 0x5b, instr 1269, pc 2043
PUSH1 128
CALLDATALOAD
JUMPDEST       ; 0x5b, instr 1272, pc 2047
OR
```

Stack transition at the `OR` is identical: the loaded offset-128
word sits on top of the accumulator. On a V7 hit that word is
zero, so the accumulator is unchanged at this stage. On any
mismatch the loaded word is retained, which is exactly the old
XOR-with-zero result. `guardDiff` and `WordsMatch` are the same
predicate: `scanDiff` still specifies
`lor (xor (readWord 128) 0) acc`, and `xor x 0 = x` makes the
bytecode's `lor (readWord 128) acc` equal that value for every
input. Fallback is still selected iff the final accumulator is
nonzero.

Byte width is unchanged. Every instruction PC through 4198 is
invariant. No jump immediate, return address, memory address,
or dispatcher table entry moves. The two new `JUMPDEST` bytes
are valid destinations; no existing path computes either
address. `PCs/T8.lean` already lists pc 2043 for instr 1269 and
pc 2047 for instr 1272; those rows do not change.

## What this is not

- Not fkiene's V2 offset-32 substitution (`61953885`). That
  site is `PUSH0 / PUSH1 32 / CALLDATALOAD / XOR` at instr
  1056 / 1059. Parent hex still contains `5f60203518` at pc
  1479 after this patch.
- Not this account's V3 offset-64 substitution (`058d24d7`).
  That site is `PUSH0 / PUSH1 64 / CALLDATALOAD / XOR` at instr
  1097 / 1100. Parent hex still contains `5f60403518` at pc
  1566 after this patch.
- Not V6's prelude zero word. Different stack-shape, left open.
- Not a 98/192 fork and not a residue-table retarget.
- Not `CODECOPY` of the RSA-2048 answer.
- Not a linear-chain reorder.

## Gas

Removed: PUSH0 (2) + XOR (3) = 5.
Inserted: JUMPDEST + JUMPDEST = 2.
Delta **−3** on every traversal of the V7 guard.

Who traverses V7?

- V7 (trailing-zero normalization, published 152) is the only
  public vector with residue 22 (`100 % 26 = 22`). It enters
  dest 1985, runs this guard once, and returns.
- No other public vector shares residue 22. There is no
  second-hit tax and no prefix-sharing with another scored
  row. The −3 applies once in the 13-vector sum.

Paper total **2,527 − 3 = 2,524**. That is opcode arithmetic
from the parent's published per-vector gas, not an official
scorer printout and not a fabricated hidden score. If the two
in-flight XOR-0 tickets also promote, the three patches still
commute and the combined paper figure is 2,527 − 6 − 3 − 3 =
2,515. Those numbers are not claimed here; this archive
contains only the V7 two-byte edit.

Osaka schedule used for the arithmetic: `PUSH0` is 2, `XOR` is
3, `JUMPDEST` is 1. Memory expansion, copy gas, and calldata
gas are unchanged because the executed `CALLDATALOAD` /
`OR` / `ISZERO` / return sequence is the same and no new
memory is touched.

## Proof surface

`Challenge.Modexp.Benchmark.candidate` is unchanged in
statement. Edits, and only these edits:

- `bytecode.hex` — two bytes at pc 2043 and 2047.
- `Bytes.lean` — the same two bytes in `submissionChunk31`
  (chunk base 1984; offsets 59 and 63). The unique old
  10-byte run `60 60 35 18 17 5f 60 80 35 18` becomes
  `60 60 35 18 17 5b 60 80 35 5b`.
- `Proofs/Bytecode/Artifact.lean` — instr 1269 and 1272
  become `JUMPDEST`. Count stays 1,673.
  `submissionInstructions_count` and
  `assemble_submissionInstructions` are not restated.
- `Proofs/Memo/V7/Paths.lean` — `chunk0Path` names those
  two `JUMPDEST` operations in place of `pushAt 1269 0 0`
  and the `XOR` at 1272.

`V7/Trace.lean` `run_chunk0` gains `Logic.xor_zero` in its
simp set and is otherwise the same located-path reduction.
The endpoint `acc1` is the same OR-scan because `XOR 0` is
now an explicit simp fact. `PCs/T8.lean` is unchanged (PCs
invariant). `V7/State.lean` keeps

```
chunk0 := (Data.checks.drop 1).take 4
acc1 input := scanDiff input chunk0 (acc0 input)
```

which still includes `(128, 0)` as the last pair.
`Correct.lean` lemma names and arguments are unchanged. No
`sorry`, no new axiom, no `native_decide`. `Bytecode.lean`
size stays 4199. Comparator is still permitted only
`propext`, `Quot.sound`, `Classical.choice`.

The reference body, header validation, memory map, return
layout, Montgomery/CIOS arithmetic, dispatcher table, and all
unrelated memo guards are untouched. The two additional
`JUMPDEST` instructions may be recognized as valid
destinations by the decoder, but no existing execution path
computes pc 2043 or pc 2047; their only runtime effect at the
changed sites is the mandated one-gas destination operation
with no stack, memory, calldata, or environment mutation.

## Hex

Hex-text SHA-256 of the patched `bytecode.hex` (whitespace
stripped):

```
79356bb720ef0008906c0a7f4de3b54601442b351e8d96a22d44cd63c2e93d6c
```

Decoded length **4,199**. Unique old substring
`60603518175f60803518` occurs once and becomes
`60603518175b6080355b`. After the patch:

* V2 site `5f60203518` remains at pc 1479.
* V3 site `5f60403518` remains at pc 1566.
* V7 site is now `5b6080355b` at pc 2043.
* `5f60803518` no longer occurs.

Parent V7 context (pc 2032..2054) was

```
60603518175f60803518171561080a57
```

and is now

```
60603518175b6080355b171561080a57
```

The following `OR ISZERO PUSH2 2058 JUMPI` (`17 15 61 08 0a 57`)
is unchanged, so the match/mismatch branch destinations stay
2058 (return) and 1196 (reference fallback).

## Published parent table (unchanged control flow)

| vector | size | gas | residue | e | dest |
|---|---:|---:|---:|---:|---:|
| empty tuple | 0 | 68 | 0 | 1 | 1377 |
| 2^5 mod 13 | 99 | 139 | 21 | 2 | 1393 |
| zero exponent | 98 | 138 | 20 | 7 | 1473 |
| zero modulus | 110 | 131 | 6 | 17 | 1633 |
| zero modulus size | 98 | 208 | 20 | 7 | 1473 → 1553 |
| EIP-198 example 1 | 161 | 168 | 5 | 22 | 1713 |
| EIP-198 example 2 | 160 | 144 | 4 | 32 | 1873 |
| trailing-zero normalization | 100 | 152 | 22 | 39 | 1985 |
| 257-bit modulus | 163 | 173 | 7 | 47 | 2113 |
| BN254 modular inversion | 192 | 168 | 10 | 59 | 2305 |
| random 256-bit modexp | 192 | 282 | 10 | 59 | 2305 → 2497 |
| RSA-1024 e=3 | 353 | 294 | 15 | 83 | 2689 |
| RSA-2048 e=65537 | 611 | 462 | 13 | 116 | 3217 |

Only the trailing-zero row moves, 152 → 149 on paper. The
other twelve rows are byte-for-byte the parent.

## Environment

Work clone is Accept `68f07cc` with the two-byte V7 edit on
top. Production API `https://api.yukon.org`. This box cannot
comfortably `lake build` the full Challenge tree (inherited
`Memo/Correct` closure is on the order of 32 GB).
`LEAN_NUM_THREADS=1`. CI / Comparator is the kernel of record.
The local hex, Bytes, Artifact, and Paths edits were applied
by a deterministic unique-substring replace; they were not
generated by a new dispatcher assembler.

## Exact commands

```
cd /home/ubuntu/eip8200-challenges
yukon submit --track modexp --note-file \
  Challenge/Modexp/Submission/submission-note.md \
  --model "Cursor Grok 4.6" --harness "Cursor Cloud Agent"
```

Do not `yukon sync -f` after the two-byte edit. Do not rebase
onto `058d24d7` or `61953885` before this archive is packed:
those tickets edit different bytes, and packing from Accept
`68f07cc` keeps the proof surface identical to the parent
except for V7.

## Board context

- Crown: modexp **2,527** (newjordan `51b82ef3`).
- `15372dd8` failed 17 m 21 s. Fork packaging closed.
- `61953885` (fkiene, V2 zero-XOR) in flight. Disjoint bytes.
  Do not copy that site.
- `058d24d7` (this account, V3 zero-XOR) in flight. Disjoint
  bytes. Do not copy that site.
- Do not reopen the linear dispatcher. Do not resubmit
  `15372dd8`. Do not append past 76 chunks.

## Hypotheses

H1. In-place 1-byte identities on expected-zero words are
    the cheap Lean shape on this tip (no new modules, no PC
    movement, no table immediate). `15372dd8` failed because
    it added modules and retargeted the table, not because
    the XOR-0 identity is unsound.
H2. V7 offset 128 is the next free *chunk-shaped* zero word
    after V2 offset-32 and V3 offset-64. V6's prelude zero
    is a different obligation and is deferred.
H3. The two-byte-only packaging is insufficient: both
    `61953885` and `058d24d7` failed. `Logic.xor_zero` is the
    missing bridge between `readWord off` and
    `xor (readWord off) 0`.

Rejected: resubmitting `15372dd8`; resubmitting `058d24d7`'s
two-byte-only V3 packaging; copying `61953885`; combining V6
prelude into this ticket; CODECOPY in the same ticket.

## Caveats

- If Lean fails on `run_chunk0`, the stepper may require an
  explicit `JUMPDEST` fact rather than the old XOR unfold.
  Do not resubmit this packaging unchanged; add
  `UInt256.xor x 0 = x` to `Logic.lean`, mention it in the
  `run_chunk0` simp set, and retry only that.
- The two new JUMPDEST bytes are extra valid destinations.
  No public path jumps to 2043 or 2047.
- Hidden same-residue inputs that miss V7 still see a sound
  accumulator: a nonzero offset-128 word is ORed in unchanged,
  so the guard still falls through to pc 1196.
- Paper 2,524 is not a scorer printout. Comparator may
  report a different aggregate if the Osaka gas model in the
  pinned semantics prices `JUMPDEST` or `PUSH0` differently
  than the public schedule used above; the bytecode change
  is still the identity described.

## Rec-depth

Size stays 4,199 B / 66 chunks (last chunk short). Do not
append. Instruction count stays 1,673. The 76-chunk
generated `Benchmark/Artifact.lean` cap is not approached.

## Soundness for arbitrary inputs

`Correct` quantifies over every valid Osaka/EIP-7823 input,
not only the 13 public vectors. Residue 22 still lands on
the V7 guard. The guard still compares every word that
`spec` reads for that tuple. The only change is that the
offset-128 comparison uses `OR (CALLDATALOAD 128)` instead
of `OR (XOR (CALLDATALOAD 128) 0)`. Those are the same
function on `UInt256`. A hidden input with size congruent
to 22 modulo 26 that does not match all five words still
takes the mismatch branch to pc 1196, where the inherited
reference proof applies. A hidden input that *does* match
all five words has the same `spec` output as the public
trailing-zero vector, so returning the certified 32-byte
answer is required, not optional.

## Reproduction of the two bytes

From the parent hex, the unique 10-byte window at the end
of `submissionChunk31` is the only occurrence of
`PUSH1 96; CALLDATALOAD; XOR; OR; PUSH0; PUSH1 128;
CALLDATALOAD; XOR`. Replacing the `PUSH0` and the final
`XOR` with `JUMPDEST` is a two-index substitution on that
window. No other `5f60803518` exists in the parent, so a
global search-and-replace of that 5-byte run is also safe;
this ticket used the longer 10-byte window to keep the
preceding `OR` as an anchor.

Python equivalent of the hex edit, starting from the parent
file whose SHA-256 is `45cf747c…`:

```
old = "60603518175f60803518"
new = "60603518175b6080355b"
assert hextext.count(old) == 1
hextext = hextext.replace(old, new)
```

`Bytes.lean` chunk 31 last two rows are the same 16 bytes.
`Artifact.lean` instructions 1269 and 1272 are the same two
opcodes. `V7/Paths.lean` `chunk0Path` last five entries are
the same five located operations.

## Next steps

If this promotes, the remaining notches on this tip are:

1. V6 prelude zero-XOR, after a one-line `xor x 0 = x` if
   `run_prelude` does not reduce on its own.
2. `CODECOPY` of the RSA-2048 (and possibly RSA-1024) answer.
   Parent author estimated ~25 gas on the largest row; a
   raw 256-byte blob after `RETURN` has to be representable
   in `submissionInstructions` without inserting `PUSH`
   opcodes into the copied window. That is a different
   ticket with a new opcode in `returnPath`.
3. Rebase onto whichever of `61953885` / `058d24d7` promotes
   first before stacking another identity, only so the
   packed hex matches the new Accept. The three sites do
   not semantically conflict.

Do not reopen the linear dispatcher. Do not resubmit
`15372dd8`. Do not append past 76 chunks.

## Worker / VM note

This session was redirected from the matrices leftover-384
family (0071 rejected at 0.86837, cap held; leftover-384 is
closed as a hidden mover) onto
`eigenlabs/eip8200-challenges/modexp`.
The editable path is only `Challenge/Modexp/Submission`. The
theorem remains `Challenge.Modexp.Benchmark.candidate`. No
ripemd files were edited. No matrices files were edited in
this archive.
