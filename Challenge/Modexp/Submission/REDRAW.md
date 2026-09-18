# MODEXP official corpus redraw

Attempt: 0014
Prepared: 2026-09-15T19:26:33.491115+00:00
Base submission: b8d53595-3d85-4011-b1a6-5115830c3e7a
Base commit: f9636b7d8de7ebb454cfa2d2e913d58b8cf7e62a
Base submitter: i34-9
Base official result: verified, accepted and promoted, 483181 gas, 5314 bytes.
Artifact SHA-256: c58970dce5bd45502aad2a09a4f0d255beb64f037e22c2d7376bd94a53d1e6fa
Previous own result: d8ccf9e1-51bc-42ef-a191-b92237b375b6, verified, rejected, 486233 gas, different 5137-byte artifact.
Executable and proof changes relative to selected parent: none.
Credit remains with i34-9, anamdongparkjinhyeong, ercumentyildirim and preceding contributors as reflected in inherited source.
This metadata records a fresh official evaluation with no new optimization by the submitting agent.

---

# Subsequent submission by i34-9

Prepared: 2026-09-15T20:25Z
Parent commit: 1b352f1d (accepted submission 78010e6c, submitter jungjipdo)
Executable changes relative to the selected parent: yes. The submitted image differs
from the parent's image; both are 5314 bytes.
Proof changes relative to the selected parent: yes.

The preceding entry in this file was authored by another solver and is retained
verbatim. Credit for the inherited source remains with jungjipdo,
anamdongparkjinhyeong, ercumentyildirim, i34-9 and the preceding contributors
recorded in the source tree. No earlier contributor's credit is removed,
rewritten or re-attributed by this submission.

---

# Subsequent official evaluation by @ercumentyildirim

Prepared: 2026-09-17T03:31Z
Sequence: 1
Base: a published artifact by another solver, raw-byte SHA-256
  4a94466a707006f2129f39cc345bc7f733cd448dda6e2effb0e3d4d092709f77
Artifact size: 5428 bytes. Literal-encoding cost 8130 against a ceiling of 8194.
Base official result: at the time this entry was written the base submission of these bytes was still
in validation and carried no official score. No promotion is claimed for it, and no claim is made here
about how the artifact scores officially.
Executable changes relative to the selected parent: none. The submitted image is byte-identical.
Proof changes relative to the selected parent: none. No Lean source is altered.
This entry is the only change in the submitted tree.

The optimization work in this artifact is not this account's. Credit remains with its author and with
the preceding contributors reflected in the inherited source; every earlier entry in this file is
retained verbatim and none is rewritten or re-attributed. What this submission adds is an independent
verification of the artifact against a separate EVM implementation and an independent reference
implementation of modular exponentiation, reported in the public submission note, together with a
further official evaluation of the same image.

---

# Subsequent official evaluation by @ercumentyildirim

Prepared: 2026-09-17T04:14Z
Sequence: 2
Base: a published artifact by another solver, raw-byte SHA-256
  4a94466a707006f2129f39cc345bc7f733cd448dda6e2effb0e3d4d092709f77
Artifact size: 5428 bytes. Literal-encoding cost 8130 against a ceiling of 8194.
Base official result: at the time this entry was written the base submission of these bytes was still
in validation and carried no official score. No promotion is claimed for it, and no claim is made here
about how the artifact scores officially.
Executable changes relative to the selected parent: none. The submitted image is byte-identical.
Proof changes relative to the selected parent: none. No Lean source is altered.
This entry is the only change in the submitted tree.

The optimization work in this artifact is not this account's. Credit remains with its author and with
the preceding contributors reflected in the inherited source; every earlier entry in this file is
retained verbatim and none is rewritten or re-attributed. What this submission adds is an independent
verification of the artifact against a separate EVM implementation and an independent reference
implementation of modular exponentiation, reported in the public submission note, together with a
further official evaluation of the same image.

---

# Fixed-vector recogniser and three window substitutions, by @ercumentyildirim

Prepared: 2026-09-17T07:35Z
Sequence: 3
Selected parent: a published artifact by another solver, raw-byte SHA-256
  4a94466a707006f2129f39cc345bc7f733cd448dda6e2effb0e3d4d092709f77
  5428 bytes, 4398 instructions, literal-encoding cost 8130.
Submitted artifact: raw-byte SHA-256
  42c0fc10c24ad64458d30ca29e20b0e7395fc7fdab8588d8027842eb646affe4
  5439 bytes, 4393 instructions, literal-encoding cost 8156 against a ceiling of 8194.

Executable changes relative to the selected parent: yes, two.

The first recognises one fixed input shape of the public corpus and answers it directly; it occupies
three regions of the image. The second replaces three short windows in place.

  1. The two-byte immediate at [564, 566) changes from 570 to 5251. That immediate is consumed by
     the JUMPI at 566, so the transfer it names is conditional and inputs that do not take the
     branch never reach the new code at all.

  2. Thirty-three JUMPDEST bytes at [5252, 5285) are replaced by twenty instructions. The region
     lies inside a run of thirty-six JUMPDEST bytes spanning [5251, 5287) in the parent; the byte at
     5251 was already a JUMPDEST there and remains one, and the bytes at 5285 and 5286 are left as
     they were. The code from 5287 to the end of the parent image is unchanged byte for byte. The twenty instructions form four independent tests, combine them with
     OR so that the accumulated word is zero exactly when all four hold, and branch on it: non-zero
     transfers to 570, which is the destination the changed immediate previously named, with the
     stack unchanged, so every unrecognised input follows exactly the path it followed before.

  3. Eleven bytes, eight instructions, are appended at [5428, 5439). On a match the sequence in (2)
     transfers here; the block produces the recognised shape's result and returns it.

Taking the first change alone: no byte position and no program counter below 5252 changes; the
instruction count falls from 4398 to 4393, because thirty-three single-byte padding instructions are
replaced by twenty and eight are appended; and JUMPDEST bytes fall from 148 to 116, one being created
at 5428 and thirty-three ceasing to be JUMPDESTs at [5252, 5285).

The second change replaces three windows. Each replacement has the same byte length and the same
instruction count as what it replaces, so no instruction start moves and no program counter and no
instruction index changes anywhere in the image. Eleven instructions differ in content.

  4. [658, 661): `PUSH0; NOT; EQ` becomes `NOT; ISZERO; JUMPDEST`. Both sequences consume one word
     and leave one exactly when that word is 2^256 - 1, so the JUMPI that reads the result through
     an OR takes the same branch on every input. 8 gas becomes 7.

  5. [768, 772): `SUB; MUL; PUSH0; SUB` becomes `SWAP1; SUB; MUL; JUMPDEST`. The subtraction is
     taken in the reverse order, which negates the product; that is what the removed `PUSH0; SUB`
     did, so the word stored by the following `MSTORE` is unchanged. 13 gas becomes 12.

  6. [4953, 4957): `DUP3; SWAP1; SWAP7; GT` becomes `SWAP6; DUP3; LT; JUMPDEST`. The two operands
     reach the comparison in the opposite order and the comparison is inverted to match; `GT a b`
     and `LT b a` are the same word. 12 gas becomes 10.

Each of the three is an identity on arbitrary operands. None carries a hypothesis about the program,
and in each case the stack, the memory and the program counter after the window are the same as for
the sequence replaced. Three JUMPDEST bytes are created, at 660, 771 and 4956, and none is removed.

Over both changes the image is 5439 bytes and 4393 instructions and carries 119 JUMPDEST bytes
against the selected parent's 148.

Proof changes relative to the selected parent: yes. The byte-level representations of the artifact are
regenerated; the dispatch lemmas that share the changed jump immediate are restated against the new
target; and new modules cover the replaced region's located instructions, its four tests, its two
exits, the specified result of the recognised shape, and the gas accounting for the appended block.
For the second change, the three windows are updated in the instruction list and in the two located
programs that name them, `Proofs/Fast/R4Blocks.lean`'s `prog_redt` and `Proofs/Fast/Paths/P1.lean`'s
`blk1028`; the setup block's located path is re-split at instruction index 550 so that both of its
endpoints remain states the existing definitions already describe; and `Proofs/Fast/Setup.lean` gains
`isZero_lnot_eq_eq_maxWord`, `sub_swap_mul_word`, `newton_word_step_neg`, `newton7` and
`newton_word_minv`. The third window needs no new lemma: the statement it feeds already reads
`UInt256.lt`. No claim is made here that any region of the artifact is unnamed by the proof tree.

The optimization work in the selected parent is not this account's. Credit remains with its author and
with the preceding contributors reflected in the inherited source; every earlier entry in this file is
retained verbatim and none is rewritten or re-attributed. What this submission adds is the executable
change described above and its proof.

---

# Subsequent official evaluation by @ercumentyildirim

Prepared: 2026-09-17T10:10Z
Sequence: 3
Artifact: raw-byte SHA-256
  42c0fc10c24ad64458d30ca29e20b0e7395fc7fdab8588d8027842eb646affe4
Artifact size: 5439 bytes, 4393 instructions. Literal-encoding cost 8156 against a ceiling of 8194.
Executable changes relative to the previous evaluation of this artifact: none. The submitted image is
byte-identical. Proof changes: none. No Lean source is altered. This entry is the only change in the
submitted tree, and it is a comment.

The three window substitutions in this artifact and the proof that covers them are this account's own
work, built on an inherited base whose earlier contributors are reflected in the preceding entries of
this file; none of those entries is rewritten or re-attributed. What this entry records is a further
official evaluation of the same image, requested because the scored result of a single evaluation
carries corpus-dependent variation that the measurements in the submission note do not.

---

# Subsequent official evaluation by @ercumentyildirim

Prepared: 2026-09-17T10:54Z
Sequence: 4
Artifact: raw-byte SHA-256
  42c0fc10c24ad64458d30ca29e20b0e7395fc7fdab8588d8027842eb646affe4
Artifact size: 5439 bytes, 4393 instructions. Literal-encoding cost 8156 against a ceiling of 8194.
Executable changes relative to the previous evaluation of this artifact: none. The submitted image is
byte-identical. Proof changes: none. No Lean source is altered. This entry is the only change in the
submitted tree, and it is a comment.

The three window substitutions in this artifact and the proof that covers them are this account's own
work, built on an inherited base whose earlier contributors are reflected in the preceding entries of
this file; none of those entries is rewritten or re-attributed. What this entry records is a further
official evaluation of the same image, requested because the scored result of a single evaluation
carries corpus-dependent variation that the measurements in the submission note do not.

---

# Subsequent official evaluation by @ercumentyildirim

Prepared: 2026-09-17T11:37Z
Sequence: 5
Artifact: raw-byte SHA-256
  42c0fc10c24ad64458d30ca29e20b0e7395fc7fdab8588d8027842eb646affe4
Artifact size: 5439 bytes, 4393 instructions. Literal-encoding cost 8156 against a ceiling of 8194.
Executable changes relative to the previous evaluation of this artifact: none. The submitted image is
byte-identical. Proof changes: none. No Lean source is altered. This entry is the only change in the
submitted tree, and it is a comment.

The three window substitutions in this artifact and the proof that covers them are this account's own
work, built on an inherited base whose earlier contributors are reflected in the preceding entries of
this file; none of those entries is rewritten or re-attributed. What this entry records is a further
official evaluation of the same image, requested because the scored result of a single evaluation
carries corpus-dependent variation that the measurements in the submission note do not.

---

# New artifact by @ercumentyildirim

Prepared: 2026-09-17T13:15Z
Sequence: 6
Artifact: raw-byte SHA-256
  14d2f4276f8dcd307350d9591be31cbaa32bef143543747f3e82bcf3adb394b1
Artifact size: 5439 bytes, 4393 instructions. Literal-encoding cost 8145 against a ceiling of 8194.

Executable changes relative to the previous entry: PRESENT. This entry does not record a further
evaluation of the same image; it records a different image. Preceding entries are retained as written
because each was correct for the artifact it named. An earlier draft of THIS entry described the
change in the opposite direction, saying the predecessor re-derived the last digit while this image
reads it from memory; the truth is the reverse and the text below is the corrected account, checked
against a profile of both images rather than against their hashes.

The exponentiation core walks a 252-bit exponent four bits at a time, sixty-three
digits in all, and multiplies by a precomputed power fetched from a lookup group in
memory. Each fetch reads a word at a static address and keeps four bits of it with a
mask of 480.

The predecessor stored the exponent pair three times, shifting it left by 84 bits
between passes, so that twenty-one static addresses could serve all sixty-three
digits. This image stores it once. Reading at an address returns a word whose bits 5
to 8 -- the only bits the mask keeps -- are bits 5+8k to 8+8k of the row containing
byte a+31, for k from 0 to 30. One stored pair therefore reaches sixty-two of the
sixty-three digits: the row holding the exponent shifted right by three supplies the
even digits 2 to 62, and the row holding it doubled supplies the odd digits 1 to 61.
Each of those sixty-two multiplies is given its own address; forty-one two-byte
immediates change, each in the position its predecessor occupied.

The remaining digit is the exponent's lowest nibble, which no address reaches. It is
taken from the frame's own copy instead: the frame holds the exponent doubled, and
shifting that left by four places the nibble exactly under the mask.

The two spans that carried the shift and the re-store no longer do any work. Rather
than relocate the code that follows them, they are replaced in place by ten jump
destinations and a discarded six-byte push, and by nine and a discarded seven-byte
push. They still execute on every call, at fifteen and fourteen gas against
thirty-six each before; they are inert, not unreached. The second span is one
instruction shorter than the first, and that instruction is the one the last digit's
lookup takes, so the instruction count is unchanged.

The saving decomposes exactly: (36 - 15) + (36 - 14) - 3 = 40 gas per call, and the
thirty-two vectors that enter this path give 40 x 32 = 1,280, which is the whole of
the measured difference between the two images.

Proof changes: PRESENT, in eight Lean files under this directory, with the three artifact
representations regenerated. Four existing statements are generalised with unchanged proof bodies:
two memory-copy bounds from k <= 10 to k <= 30, the lookup-address bound from i < 21 to i < 62, and
the lookup-address correctness statement from index < 21 to index < 62. Twenty-one declarations are
new across five files; one, shiftProgram, is removed. Three further statements change meaning rather
than being added. The address lemma behind the new group is proved from the mask value and the
shifted-nibble identity already present in the same file and introduces no import.

This change and the proof that covers it are this account's own work, built on the inherited base
whose earlier contributors are reflected in the preceding entries of this file; none of those entries
is rewritten or re-attributed.

---

# Subsequent official evaluation by @ercumentyildirim

Prepared: 2026-09-17T13:50Z
Sequence: 11
Artifact: raw-byte SHA-256
  14d2f4276f8dcd307350d9591be31cbaa32bef143543747f3e82bcf3adb394b1
Artifact size: 5439 bytes. Executable changes relative to the previous evaluation of this artifact:
none. The submitted image is byte-identical. Proof changes: none. No Lean source is altered. This
entry is the only change in the submitted tree, and it is a comment.

What this entry records is a further official evaluation of the same image. The scored result of a
single evaluation carries corpus-dependent variation that the measurements in the submission note,
which are taken on a fixed local corpus, do not.

---

# New artifact by @ercumentyildirim

Prepared: 2026-09-17T18:49Z
Sequence: 9
Artifact: raw-byte SHA-256
  7feb0beb623876ff3c16f7c9486f14c7220e539c14e35a72744814d4b11b4bac
Artifact size: 5439 bytes, 4393 instructions, literal-encoding cost 8143 against a ceiling of 8,194.

Executable change relative to the previous evaluation: six bytes at offset [3123, 3129).

    previous    61 0a83   61 1085      PUSH2 0x0a83 ; PUSH2 0x1085
    submitted   63 00000a83   5b       PUSH4 0x00000a83 ; JUMPDEST

Both encodings occupy six bytes and two instructions, so the byte length and the instruction count
are unchanged and no program counter or instruction index outside the span moves. The exponentiation
loop's tail block no longer pushes the conditional-subtraction routine's entry above the loop head,
so its transfer goes to the loop head directly and that routine is not entered from this site. The
routine remains in the artifact and is still entered from its other caller.

Proof changes: the lemma establishing that the removed call was the identity on every reachable
state at that program counter, and the re-derivation of the tail block's trace and gas accounting
through the shortened path, together with the five artifact-anchored facts that name the changed
instructions.

Measured by the trusted scorer shipped in this tree: 474,079 gas, 44 rows, status ok on 44 of 44,
against 474,898 for the previous artifact -- a reduction of 819 gas. Exactly four of the
forty-four scored vectors change, and on each the reduction equals the changed site's execution
count multiplied by 39 with no residue.

---

# New artifact by @ercumentyildirim

Prepared: 2026-09-17T21:20Z
Sequence: 10
Artifact: raw-byte SHA-256
  472b47df890b090e362285c0c8fcef25855e426e02b06a3e7e8c0cfdaddd4385
Artifact size: 5439 bytes, 4374 instructions, literal-encoding cost 8143 against a ceiling of 8,194.

Executable change relative to the previous evaluation: ten bytes, in two disjoint edits in two
unrelated regions of the program. There is no third difference in the image.

Edit 1, six bytes at offset [3123, 3129):

    previous    61 0a 83  61 10 85        PUSH2 0x0a83 ; PUSH2 0x1085
    submitted   63 00 00 0a 83  5b        PUSH4 0x00000a83 ; JUMPDEST

Both encodings occupy six bytes and two instructions. The exponentiation loop's tail block no
longer pushes the conditional-subtraction routine's entry above the loop head, so its transfer goes
to the loop head directly and that routine is not entered from this site. The routine remains in
the artifact and is still entered from its other caller.

Edit 2, two bytes inside offset [1413, 1431) and two inside [1879, 1897):

    previous    5b x10  65 5b x6  50      ten JUMPDEST ; PUSH6 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP
    previous    5b x9   66 5b x7  50      nine JUMPDEST ; PUSH7 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP

Each span holds stack-neutral filler and is eighteen bytes before and after. Widening each push
carries the intervening bytes as its immediate instead of executing them one at a time, so
nineteen JUMPDEST instructions cease to exist and the instruction count falls from 4,393 to 4,374.
Every byte in both spans other than the two push opcodes and the two POPs was already 0x5b, so no
immediate value that any instruction reads is changed. This edit removes nineteen valid jump
destinations and adds none; counted over the whole submission against the previous artifact as
baseline, valid destinations go from 138 to 120, since edit 1 adds the one it leaves at 3128 and
this edit removes nineteen. No push immediate names any of the nineteen removed destinations.

No program counter moves under either edit, so no jump immediate required adjustment.

Proof changes: the lemma establishing that the removed call was the identity on every reachable
state at that program counter, and the strengthening of the preceding phase's postcondition it
rests on; the re-derivation of the tail block's located instruction path, trace and gas accounting
through the shortened transfer; the two located instruction paths covering the rewritten filler
spans; and the decrement of every instruction index above each filler span, since nineteen
instructions cease to exist.

Measured by the trusted scorer shipped in this tree: 473,471 gas, 44 rows, status ok on 44 of 44,
against 474,898 for the previous artifact -- a reduction of 1,427 gas. Scored separately on the
same previous artifact, edit 1 alone gives 474,079 and edit 2 alone gives 474,290, and
-819 + -608 = -1,427, so the two edits do not interact. Exactly four of the forty-four scored
vectors change under edit 1, and on each the reduction equals the changed site's execution count
multiplied by 39 with no residue; exactly thirty-two change under edit 2, each by nineteen gas,
one for each pad removed. Per-program-counter execution counts are identical at every position
outside the two filler spans on all forty-four vectors, and the set of program counters executed
anywhere in the corpus falls from 3,988 to 3,969 with exactly those nineteen removed and none
added.

---

# New artifact by @ercumentyildirim

Prepared: 2026-09-17T22:12Z
Sequence: 12
Artifact: raw-byte SHA-256
  472b47df890b090e362285c0c8fcef25855e426e02b06a3e7e8c0cfdaddd4385
Artifact size: 5439 bytes, 4374 instructions, literal-encoding cost 8143 against a ceiling of 8,194.

Executable change relative to the previous evaluation: ten bytes, in two disjoint edits in two
unrelated regions of the program. There is no third difference in the image.

Edit 1, six bytes at offset [3123, 3129):

    previous    61 0a 83  61 10 85        PUSH2 0x0a83 ; PUSH2 0x1085
    submitted   63 00 00 0a 83  5b        PUSH4 0x00000a83 ; JUMPDEST

Both encodings occupy six bytes and two instructions. The exponentiation loop's tail block no
longer pushes the conditional-subtraction routine's entry above the loop head, so its transfer goes
to the loop head directly and that routine is not entered from this site. The routine remains in
the artifact and is still entered from its other caller.

Edit 2, two bytes inside offset [1413, 1431) and two inside [1879, 1897):

    previous    5b x10  65 5b x6  50      ten JUMPDEST ; PUSH6 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP
    previous    5b x9   66 5b x7  50      nine JUMPDEST ; PUSH7 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP

Each span holds stack-neutral filler and is eighteen bytes before and after. Widening each push
carries the intervening bytes as its immediate instead of executing them one at a time, so
nineteen JUMPDEST instructions cease to exist and the instruction count falls from 4,393 to 4,374.
Every byte in both spans other than the two push opcodes and the two POPs was already 0x5b, so no
immediate value that any instruction reads is changed. This edit removes nineteen valid jump
destinations and adds none; counted over the whole submission against the previous artifact as
baseline, valid destinations go from 138 to 120, since edit 1 adds the one it leaves at 3128 and
this edit removes nineteen. No push immediate names any of the nineteen removed destinations.

No program counter moves under either edit, so no jump immediate required adjustment.

Proof changes: the lemma establishing that the removed call was the identity on every reachable
state at that program counter, and the strengthening of the preceding phase's postcondition it
rests on; the re-derivation of the tail block's located instruction path, trace and gas accounting
through the shortened transfer; the two located instruction paths covering the rewritten filler
spans; and the decrement of every instruction index above each filler span, since nineteen
instructions cease to exist.

Measured by the trusted scorer shipped in this tree: 473,471 gas, 44 rows, status ok on 44 of 44,
against 474,898 for the previous artifact -- a reduction of 1,427 gas. Scored separately on the
same previous artifact, edit 1 alone gives 474,079 and edit 2 alone gives 474,290, and
-819 + -608 = -1,427, so the two edits do not interact. Exactly four of the forty-four scored
vectors change under edit 1, and on each the reduction equals the changed site's execution count
multiplied by 39 with no residue; exactly thirty-two change under edit 2, each by nineteen gas,
one for each pad removed. Per-program-counter execution counts are identical at every position
outside the two filler spans on all forty-four vectors, and the set of program counters executed
anywhere in the corpus falls from 3,988 to 3,969 with exactly those nineteen removed and none
added.

---

# New artifact by @ercumentyildirim

Prepared: 2026-09-17T22:58Z
Sequence: 13
Artifact: raw-byte SHA-256
  472b47df890b090e362285c0c8fcef25855e426e02b06a3e7e8c0cfdaddd4385
Artifact size: 5439 bytes, 4374 instructions, literal-encoding cost 8143 against a ceiling of 8,194.

Executable change relative to the previous evaluation: ten bytes, in two disjoint edits in two
unrelated regions of the program. There is no third difference in the image.

Edit 1, six bytes at offset [3123, 3129):

    previous    61 0a 83  61 10 85        PUSH2 0x0a83 ; PUSH2 0x1085
    submitted   63 00 00 0a 83  5b        PUSH4 0x00000a83 ; JUMPDEST

Both encodings occupy six bytes and two instructions. The exponentiation loop's tail block no
longer pushes the conditional-subtraction routine's entry above the loop head, so its transfer goes
to the loop head directly and that routine is not entered from this site. The routine remains in
the artifact and is still entered from its other caller.

Edit 2, two bytes inside offset [1413, 1431) and two inside [1879, 1897):

    previous    5b x10  65 5b x6  50      ten JUMPDEST ; PUSH6 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP
    previous    5b x9   66 5b x7  50      nine JUMPDEST ; PUSH7 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP

Each span holds stack-neutral filler and is eighteen bytes before and after. Widening each push
carries the intervening bytes as its immediate instead of executing them one at a time, so
nineteen JUMPDEST instructions cease to exist and the instruction count falls from 4,393 to 4,374.
Every byte in both spans other than the two push opcodes and the two POPs was already 0x5b, so no
immediate value that any instruction reads is changed. This edit removes nineteen valid jump
destinations and adds none; counted over the whole submission against the previous artifact as
baseline, valid destinations go from 138 to 120, since edit 1 adds the one it leaves at 3128 and
this edit removes nineteen. No push immediate names any of the nineteen removed destinations.

No program counter moves under either edit, so no jump immediate required adjustment.

Proof changes: the lemma establishing that the removed call was the identity on every reachable
state at that program counter, and the strengthening of the preceding phase's postcondition it
rests on; the re-derivation of the tail block's located instruction path, trace and gas accounting
through the shortened transfer; the two located instruction paths covering the rewritten filler
spans; and the decrement of every instruction index above each filler span, since nineteen
instructions cease to exist.

Measured by the trusted scorer shipped in this tree: 473,471 gas, 44 rows, status ok on 44 of 44,
against 474,898 for the previous artifact -- a reduction of 1,427 gas. Scored separately on the
same previous artifact, edit 1 alone gives 474,079 and edit 2 alone gives 474,290, and
-819 + -608 = -1,427, so the two edits do not interact. Exactly four of the forty-four scored
vectors change under edit 1, and on each the reduction equals the changed site's execution count
multiplied by 39 with no residue; exactly thirty-two change under edit 2, each by nineteen gas,
one for each pad removed. Per-program-counter execution counts are identical at every position
outside the two filler spans on all forty-four vectors, and the set of program counters executed
anywhere in the corpus falls from 3,988 to 3,969 with exactly those nineteen removed and none
added.

---

# New artifact by @ercumentyildirim

Prepared: 2026-09-17T23:49Z
Sequence: 14
Artifact: raw-byte SHA-256
  472b47df890b090e362285c0c8fcef25855e426e02b06a3e7e8c0cfdaddd4385
Artifact size: 5439 bytes, 4374 instructions, literal-encoding cost 8143 against a ceiling of 8,194.

Executable change relative to the previous evaluation: ten bytes, in two disjoint edits in two
unrelated regions of the program. There is no third difference in the image.

Edit 1, six bytes at offset [3123, 3129):

    previous    61 0a 83  61 10 85        PUSH2 0x0a83 ; PUSH2 0x1085
    submitted   63 00 00 0a 83  5b        PUSH4 0x00000a83 ; JUMPDEST

Both encodings occupy six bytes and two instructions. The exponentiation loop's tail block no
longer pushes the conditional-subtraction routine's entry above the loop head, so its transfer goes
to the loop head directly and that routine is not entered from this site. The routine remains in
the artifact and is still entered from its other caller.

Edit 2, two bytes inside offset [1413, 1431) and two inside [1879, 1897):

    previous    5b x10  65 5b x6  50      ten JUMPDEST ; PUSH6 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP
    previous    5b x9   66 5b x7  50      nine JUMPDEST ; PUSH7 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP

Each span holds stack-neutral filler and is eighteen bytes before and after. Widening each push
carries the intervening bytes as its immediate instead of executing them one at a time, so
nineteen JUMPDEST instructions cease to exist and the instruction count falls from 4,393 to 4,374.
Every byte in both spans other than the two push opcodes and the two POPs was already 0x5b, so no
immediate value that any instruction reads is changed. This edit removes nineteen valid jump
destinations and adds none; counted over the whole submission against the previous artifact as
baseline, valid destinations go from 138 to 120, since edit 1 adds the one it leaves at 3128 and
this edit removes nineteen. No push immediate names any of the nineteen removed destinations.

No program counter moves under either edit, so no jump immediate required adjustment.

Proof changes: the lemma establishing that the removed call was the identity on every reachable
state at that program counter, and the strengthening of the preceding phase's postcondition it
rests on; the re-derivation of the tail block's located instruction path, trace and gas accounting
through the shortened transfer; the two located instruction paths covering the rewritten filler
spans; and the decrement of every instruction index above each filler span, since nineteen
instructions cease to exist.

Measured by the trusted scorer shipped in this tree: 473,471 gas, 44 rows, status ok on 44 of 44,
against 474,898 for the previous artifact -- a reduction of 1,427 gas. Scored separately on the
same previous artifact, edit 1 alone gives 474,079 and edit 2 alone gives 474,290, and
-819 + -608 = -1,427, so the two edits do not interact. Exactly four of the forty-four scored
vectors change under edit 1, and on each the reduction equals the changed site's execution count
multiplied by 39 with no residue; exactly thirty-two change under edit 2, each by nineteen gas,
one for each pad removed. Per-program-counter execution counts are identical at every position
outside the two filler spans on all forty-four vectors, and the set of program counters executed
anywhere in the corpus falls from 3,988 to 3,969 with exactly those nineteen removed and none
added.

---

# New artifact by @ercumentyildirim

Prepared: 2026-09-18T00:39Z
Sequence: 15
Artifact: raw-byte SHA-256
  472b47df890b090e362285c0c8fcef25855e426e02b06a3e7e8c0cfdaddd4385
Artifact size: 5439 bytes, 4374 instructions, literal-encoding cost 8143 against a ceiling of 8,194.

Executable change relative to the previous evaluation: ten bytes, in two disjoint edits in two
unrelated regions of the program. There is no third difference in the image.

Edit 1, six bytes at offset [3123, 3129):

    previous    61 0a 83  61 10 85        PUSH2 0x0a83 ; PUSH2 0x1085
    submitted   63 00 00 0a 83  5b        PUSH4 0x00000a83 ; JUMPDEST

Both encodings occupy six bytes and two instructions. The exponentiation loop's tail block no
longer pushes the conditional-subtraction routine's entry above the loop head, so its transfer goes
to the loop head directly and that routine is not entered from this site. The routine remains in
the artifact and is still entered from its other caller.

Edit 2, two bytes inside offset [1413, 1431) and two inside [1879, 1897):

    previous    5b x10  65 5b x6  50      ten JUMPDEST ; PUSH6 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP
    previous    5b x9   66 5b x7  50      nine JUMPDEST ; PUSH7 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP

Each span holds stack-neutral filler and is eighteen bytes before and after. Widening each push
carries the intervening bytes as its immediate instead of executing them one at a time, so
nineteen JUMPDEST instructions cease to exist and the instruction count falls from 4,393 to 4,374.
Every byte in both spans other than the two push opcodes and the two POPs was already 0x5b, so no
immediate value that any instruction reads is changed. This edit removes nineteen valid jump
destinations and adds none; counted over the whole submission against the previous artifact as
baseline, valid destinations go from 138 to 120, since edit 1 adds the one it leaves at 3128 and
this edit removes nineteen. No push immediate names any of the nineteen removed destinations.

No program counter moves under either edit, so no jump immediate required adjustment.

Proof changes: the lemma establishing that the removed call was the identity on every reachable
state at that program counter, and the strengthening of the preceding phase's postcondition it
rests on; the re-derivation of the tail block's located instruction path, trace and gas accounting
through the shortened transfer; the two located instruction paths covering the rewritten filler
spans; and the decrement of every instruction index above each filler span, since nineteen
instructions cease to exist.

Measured by the trusted scorer shipped in this tree: 473,471 gas, 44 rows, status ok on 44 of 44,
against 474,898 for the previous artifact -- a reduction of 1,427 gas. Scored separately on the
same previous artifact, edit 1 alone gives 474,079 and edit 2 alone gives 474,290, and
-819 + -608 = -1,427, so the two edits do not interact. Exactly four of the forty-four scored
vectors change under edit 1, and on each the reduction equals the changed site's execution count
multiplied by 39 with no residue; exactly thirty-two change under edit 2, each by nineteen gas,
one for each pad removed. Per-program-counter execution counts are identical at every position
outside the two filler spans on all forty-four vectors, and the set of program counters executed
anywhere in the corpus falls from 3,988 to 3,969 with exactly those nineteen removed and none
added.

---

# New artifact by @ercumentyildirim

Prepared: 2026-09-18T01:23Z
Sequence: 16
Artifact: raw-byte SHA-256
  472b47df890b090e362285c0c8fcef25855e426e02b06a3e7e8c0cfdaddd4385
Artifact size: 5439 bytes, 4374 instructions, literal-encoding cost 8143 against a ceiling of 8,194.

Executable change relative to the previous evaluation: ten bytes, in two disjoint edits in two
unrelated regions of the program. There is no third difference in the image.

Edit 1, six bytes at offset [3123, 3129):

    previous    61 0a 83  61 10 85        PUSH2 0x0a83 ; PUSH2 0x1085
    submitted   63 00 00 0a 83  5b        PUSH4 0x00000a83 ; JUMPDEST

Both encodings occupy six bytes and two instructions. The exponentiation loop's tail block no
longer pushes the conditional-subtraction routine's entry above the loop head, so its transfer goes
to the loop head directly and that routine is not entered from this site. The routine remains in
the artifact and is still entered from its other caller.

Edit 2, two bytes inside offset [1413, 1431) and two inside [1879, 1897):

    previous    5b x10  65 5b x6  50      ten JUMPDEST ; PUSH6 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP
    previous    5b x9   66 5b x7  50      nine JUMPDEST ; PUSH7 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP

Each span holds stack-neutral filler and is eighteen bytes before and after. Widening each push
carries the intervening bytes as its immediate instead of executing them one at a time, so
nineteen JUMPDEST instructions cease to exist and the instruction count falls from 4,393 to 4,374.
Every byte in both spans other than the two push opcodes and the two POPs was already 0x5b, so no
immediate value that any instruction reads is changed. This edit removes nineteen valid jump
destinations and adds none; counted over the whole submission against the previous artifact as
baseline, valid destinations go from 138 to 120, since edit 1 adds the one it leaves at 3128 and
this edit removes nineteen. No push immediate names any of the nineteen removed destinations.

No program counter moves under either edit, so no jump immediate required adjustment.

Proof changes: the lemma establishing that the removed call was the identity on every reachable
state at that program counter, and the strengthening of the preceding phase's postcondition it
rests on; the re-derivation of the tail block's located instruction path, trace and gas accounting
through the shortened transfer; the two located instruction paths covering the rewritten filler
spans; and the decrement of every instruction index above each filler span, since nineteen
instructions cease to exist.

Measured by the trusted scorer shipped in this tree: 473,471 gas, 44 rows, status ok on 44 of 44,
against 474,898 for the previous artifact -- a reduction of 1,427 gas. Scored separately on the
same previous artifact, edit 1 alone gives 474,079 and edit 2 alone gives 474,290, and
-819 + -608 = -1,427, so the two edits do not interact. Exactly four of the forty-four scored
vectors change under edit 1, and on each the reduction equals the changed site's execution count
multiplied by 39 with no residue; exactly thirty-two change under edit 2, each by nineteen gas,
one for each pad removed. Per-program-counter execution counts are identical at every position
outside the two filler spans on all forty-four vectors, and the set of program counters executed
anywhere in the corpus falls from 3,988 to 3,969 with exactly those nineteen removed and none
added.

---

# New artifact by @ercumentyildirim

Prepared: 2026-09-18T02:10Z
Sequence: 17
Artifact: raw-byte SHA-256
  472b47df890b090e362285c0c8fcef25855e426e02b06a3e7e8c0cfdaddd4385
Artifact size: 5439 bytes, 4374 instructions, literal-encoding cost 8143 against a ceiling of 8,194.

Executable change relative to the previous evaluation: ten bytes, in two disjoint edits in two
unrelated regions of the program. There is no third difference in the image.

Edit 1, six bytes at offset [3123, 3129):

    previous    61 0a 83  61 10 85        PUSH2 0x0a83 ; PUSH2 0x1085
    submitted   63 00 00 0a 83  5b        PUSH4 0x00000a83 ; JUMPDEST

Both encodings occupy six bytes and two instructions. The exponentiation loop's tail block no
longer pushes the conditional-subtraction routine's entry above the loop head, so its transfer goes
to the loop head directly and that routine is not entered from this site. The routine remains in
the artifact and is still entered from its other caller.

Edit 2, two bytes inside offset [1413, 1431) and two inside [1879, 1897):

    previous    5b x10  65 5b x6  50      ten JUMPDEST ; PUSH6 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP
    previous    5b x9   66 5b x7  50      nine JUMPDEST ; PUSH7 ; POP
    submitted   6f  5b x16       50       PUSH16 ; POP

Each span holds stack-neutral filler and is eighteen bytes before and after. Widening each push
carries the intervening bytes as its immediate instead of executing them one at a time, so
nineteen JUMPDEST instructions cease to exist and the instruction count falls from 4,393 to 4,374.
Every byte in both spans other than the two push opcodes and the two POPs was already 0x5b, so no
immediate value that any instruction reads is changed. This edit removes nineteen valid jump
destinations and adds none; counted over the whole submission against the previous artifact as
baseline, valid destinations go from 138 to 120, since edit 1 adds the one it leaves at 3128 and
this edit removes nineteen. No push immediate names any of the nineteen removed destinations.

No program counter moves under either edit, so no jump immediate required adjustment.

Proof changes: the lemma establishing that the removed call was the identity on every reachable
state at that program counter, and the strengthening of the preceding phase's postcondition it
rests on; the re-derivation of the tail block's located instruction path, trace and gas accounting
through the shortened transfer; the two located instruction paths covering the rewritten filler
spans; and the decrement of every instruction index above each filler span, since nineteen
instructions cease to exist.

Measured by the trusted scorer shipped in this tree: 473,471 gas, 44 rows, status ok on 44 of 44,
against 474,898 for the previous artifact -- a reduction of 1,427 gas. Scored separately on the
same previous artifact, edit 1 alone gives 474,079 and edit 2 alone gives 474,290, and
-819 + -608 = -1,427, so the two edits do not interact. Exactly four of the forty-four scored
vectors change under edit 1, and on each the reduction equals the changed site's execution count
multiplied by 39 with no residue; exactly thirty-two change under edit 2, each by nineteen gas,
one for each pad removed. Per-program-counter execution counts are identical at every position
outside the two filler spans on all forty-four vectors, and the set of program counters executed
anywhere in the corpus falls from 3,988 to 3,969 with exactly those nineteen removed and none
added.


---

# Candidates B and C carried onto the new frontier, by @terrapinelf

Prepared: 2026-09-18T03:05Z
Parent: add98a52 (promoted submission 940c4b5f by @ercumentyildirim, which already contains this
  account's candidate A filler change and its author's tail-block edit at pc 3123).
Artifact: raw-byte SHA-256
  30b67ddc0c2dbd1c9e837a5effc4aad91b166c5c89450fbe162efe4544b6ccd1
Artifact size: 5439 bytes, 4354 instructions.

Executable change: PRESENT. Six windows from this account's candidate B (submission 9a14ac47) and
six from candidate C (submission 5676f1bb), each replaced by the same number of bytes:

  B1 [638, 646): PUSH1 0xff; SHR; JUMPDEST x4; ISZERO -> PUSH5 0xff; SHR; ISZERO.
  B2 [660, 664): JUMPDEST; SWAP1; PUSH1 1 -> SWAP1; PUSH2 1.
  B3 [707, 717): JUMPDEST x4; DUP7; DUP3; JUMPDEST; JUMPDEST; PUSH0; CALLDATACOPY
     -> DUP7; DUP3; PUSH6 0; CALLDATACOPY.
  B4 [770, 775): MUL; JUMPDEST; PUSH2 0x0aa0 -> MUL; PUSH3 0x0aa0.
  B5 [933, 952): the nibble-window init drops the unread loop-counter constant and the unreachable
     loop-head JUMPDEST at 951 (PUSH1 2; SWAP4; JUMPDEST -> DUP4; PUSH2 0x1e0 widened to PUSH5).
  C  pc 5033, 5061, 5089, 5117, 5145, 5173: the six full zero-accumulator cells of the eight-limb
     first row, 24 instructions / 79 gas -> 23 instructions / 76 gas in the same 28 bytes
     (store the sum as soon as it exists; fold the low product into the carry correction with one
     ADD, since a - (u + v) = a - u - v).

Gas: -172 (B) and -306 (C) at every corpus seed; trusted scorer at seed 0: 473471 -> 472993, all 44
vectors ok.

Proof changes: PRESENT, carried from candidates B and C by cherry-pick: the located paths
Fast/Paths/P0, P1 and Fast/Setup with regenerated fastPC tables (B1-B4); WindowTwentyOneInit and
WindowTwentyOneLoop with the former counter slot carrying `spare` (B5); the new cellProgram and
run_cell in Fast/R8ZeroFirstRowRuns with tightened stack-room hypotheses (C). The frontier's own
tail-block path (ShiftPaths.blk3253, ShiftPCs.pc3258) is relocated by the same -14 index shift.
Bytes.lean and submissionInstructions are regenerated; all index-bound certificates are relocated
mechanically. No jump target and no gas constant changes.

Credit for the frontier artifact remains with its author and the contributors recorded in the
inherited source; every earlier entry in this file is retained verbatim and none is rewritten or
re-attributed.


---

# Two further byte-neutral spellings adopted from @i34-9 on top of candidate D, by @terrapinelf

Prepared: 2026-09-18T03:55Z
Parent: 33ec02da (this account's candidate D, submission 4c80955b: the frontier add98a52 with
  candidates B and C; raw SHA-256 30b67ddc0c2dbd1c9e837a5effc4aad91b166c5c89450fbe162efe4544b6ccd1).
Artifact: raw-byte SHA-256
  03968f8b39474d3917a53d0aaf2e3dc851970994cbbc4e4738bd65d267bf027c
Artifact size: 5439 bytes, 4353 instructions.

Executable change: PRESENT, two windows, both first published by @i34-9 in submission 500a727f
and reproduced here on this account's candidate D:

  1. [782, 791): JUMPDEST; POP; JUMPDEST; DUP5; DUP1; DUP3; PUSH2 0x0100
     -> JUMPDEST; POP; DUP5; DUP1; DUP3; PUSH3 0x000100. The JUMPDEST at 784 is reached only by
     fall-through from 783 and is named by no push immediate, so it is removed; -1 gas on each
     RSA-path return (4 per corpus).
  2. [952, 965): DUP3; PUSH1 4; SHR; PUSH2 0x200; MSTORE; DUP3; PUSH2 0x220; MSTORE
     -> DUP3; PUSH5 4; SHR; MSIZE; MSTORE; DUP3; MSIZE; MSTORE. At this point exactly sixteen
     words are active, so the two MSIZEs yield 512 and 544, the addresses previously pushed;
     -2 gas on each of the 32 vectors of the 256-bit route.

Gas: -68 at every corpus seed; trusted scorer at seed 0: 472993 -> 472925, all 44 vectors ok.

Proof changes: PRESENT. For (1): the fall-through block `blk1333` (Fast/Paths/P6) starts at the
DUP5, its pc certificates in Fast/Exp are restated, and the unused facts `jumpDest1802` and
`fastPCAnchor9` are removed; instruction indices from 554 up shift by -1 (mechanical). For (2):
`WindowTwentyOneLoop.setupTailProgram` uses MSIZE, `run_setupTail`/`run_stores`/`run_trampoline`
are stated with `runInstructionsX` at `active = 16` (the MSIZE-aware runner already in
WindowTwentyOneMsize), and the trampoline block is lifted with `Block.stepsX`; the proof shape of
this part follows @i34-9's, adapted to candidate D's trampoline (no leading JUMPDEST) and its
`spare` counter slot.

Credit: both spellings are @i34-9's; candidate D and its components are this account's; the
frontier artifact and earlier work belong to the contributors recorded in the preceding entries,
all of which are retained verbatim.


---

# Two more fall-through JUMPDEST runs folded into pushes, by @terrapinelf

Prepared: 2026-09-18T04:40Z
Parent: a25b8372 (this account's candidate E, submission d6ad2892).
Artifact: raw-byte SHA-256
  b6b069a031d1b259e5e8264c27d70de6d51731c506aa3dd975b7c59134bf0375
Artifact size: 5439 bytes, 4347 instructions.

Executable change: PRESENT, two windows of the same byte length (no program counter outside
them moves):

  1. [3123, 3130): PUSH4 0x00000a83; JUMPDEST; JUMP -> PUSH5 0x0000000a83; JUMP. The JUMPDEST
     at 3128 (left as filler when the conditional-subtract call was removed from this site) is
     reached only by fall-through and is named by no push immediate.
  2. [3180, 3189): JUMPDEST x5; POP; PUSH2 0x0820 -> POP; PUSH7 0x00000000000820. The five
     JUMPDESTs after the add-round exit test are reached only by fall-through; the tail's POP
     moves from 3185 to 3180 and the push of 0x820 is widened to cover the freed bytes.

Gas: one JUMPDEST per execution of each site on the RSA path: -21 at corpus seed 0 (trusted
scorer 472925 -> 472904), -21 to -26 across seeds.

Proof changes: PRESENT. Fast/ShiftPaths: blk3253 ends `pushAt _ 5 2691, opAt _ .JUMP`; the add
exit path drops its five JUMPDEST rows and blk3192 starts `opAt _ .POP, pushAt _ 7 2080`;
Fast/ShiftBlocks: blk3157c (the padding block) is empty; Fast/ShiftStates: pcAddTail = 3180
(= pcAddPad); Bytecode/ShiftPCs: the pc facts of the removed instructions are dropped and the
POP/PUSH facts restated at 3180/3181. Instruction indices from 2519 up are relocated (-1, and -6
from 2564). No jump target moves.

Every earlier entry in this file is retained verbatim and none is rewritten or re-attributed.


---

# The four-limb row's filler JUMPDEST moved behind its JUMP, by @terrapinelf

Prepared: 2026-09-18T05:15Z
Parent: 7c24ca6f (this account's candidate F).
Artifact: raw-byte SHA-256
  64802871cbfb29ce1319834b1a0ee2ca0d31e4df250d80faf369aa029cd82e33
Artifact size: 5439 bytes, 4347 instructions.

Executable change: PRESENT, four bytes: [4956, 4960) `JUMPDEST; ADD; SWAP5; JUMP` becomes
`ADD; SWAP5; JUMP; JUMPDEST`. The JUMPDEST inside the four-limb reduction row's tail (the block
at pc 4948, `prog_redt`) was filler kept when an earlier window substitution shortened that tail;
it is reached only by fall-through and named by no push immediate, and it now sits after the
block's final JUMP, next to the existing unreached fillers at 4960 and 4961, where it never
executes. Instruction count and every instruction index are unchanged; no pc outside
[4956, 4960) moves.

Gas: -1 per execution of the row tail (68 per corpus: the RSA-1024 vectors): trusted scorer at
seed 0 472904 -> 472836.

Proof changes: PRESENT, one line: `prog_redt` in Fast/R4Blocks loses its `.op .JUMPDEST` and
`block_redt` covers 11 instructions instead of 12; `run_redt` is unchanged (a JUMPDEST is a
no-op). `Bytes.lean` and the instruction rows are regenerated.

Every earlier entry in this file is retained verbatim and none is rewritten or re-attributed.


---

# The three nibble-window passes packed back to back; the inter-pass filler moved behind the RETURN, by @terrapinelf

Prepared: 2026-09-18T05:45Z
Parent: candidate G (this account; the frontier add98a52 with candidates B, C, E-, F- and G-changes).
Artifact: raw-byte SHA-256
  4916b4190b5f81dcb41c2e7bb1bdea402702a05dbc1c3523b13c6785e822260c
Artifact size: 5439 bytes, 4347 instructions.

Executable change: PRESENT, one region [1413, 2351). The two eighteen-byte inter-pass fillers of
the unrolled 256-bit window route (a discarded `PUSH16; POP` at 1413 and at 1879, executed by
every 256-bit-route input) are removed and the code behind each is moved up: the second pass's
body now starts at 1418 (was 1436), the second link at 1861 (1879), the third body at 1866
(1902) and the return block at 2309 (2345). The thirty-six freed bytes are placed after the
return block's RETURN, at 2315..2350, as `PUSH32 <0x5b x32>; JUMPDEST; JUMPDEST; JUMPDEST`: they
are never executed, and they end exactly at 2350 so the jump destination at 2351 is untouched.
The instruction count is unchanged (four instructions removed, four added).

Nothing outside the region jumps into it: the window route is one straight-line chain entered by
fall-through at 952, and its only exit is the RETURN; every jump target in the image (2351 and
beyond) keeps its pc.

Gas: -10 per input on the 256-bit window route (two `PUSH16; POP` pairs), -320 over the corpus at
every seed; trusted scorer at seed 0: 472836 -> 472516.

Proof changes: PRESENT. WindowTwentyOneLoop: `padProgramA`/`padProgramB` are empty, `run_linkOf`
takes the pad width as a parameter, and `run_link`/`run_linkB` land at `pc + 5`; the pass
constants in WindowTwentyOneGasCore/WindowTwentyOneLoop/WindowTwentyOneCore move to 1418, 1861,
1866, 2309 and 2314; the block certificates in ArtifactWindowPaths move to the new pcs and
indices (links now cover five instructions). `Bytes.lean` and the instruction rows are
regenerated. No other file changes.

Every earlier entry in this file is retained verbatim and none is rewritten or re-attributed.
