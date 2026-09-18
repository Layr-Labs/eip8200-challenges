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

Prepared: 2026-09-17T12:55Z
Sequence: 6
Artifact: raw-byte SHA-256
  14d2f4276f8dcd307350d9591be31cbaa32bef143543747f3e82bcf3adb394b1
Artifact size: 5439 bytes, 4393 instructions. Literal-encoding cost 8145 against a ceiling of 8194.

Executable changes relative to the previous entry: PRESENT. This entry does not record a further
evaluation of the same image; it records a different image, and the preceding entries are retained as
written because each was correct for the artifact it named.

The predecessor image named in entry 5 addressed the exponentiation core's lookup group as a
twenty-one entry structure and served the final nibble of each group from a separate tail that
re-derived its operand. This image widens the group so that one addressing rule covers the whole
window and folds the tail into it: the address is computed by the mask-and-shift already present, and
the two operands the last nibble consumes are components of the frame the enclosing program already
binds. The group's contents are unchanged and no memory word is added.

The change is byte-count neutral and instruction-count neutral against the predecessor, which is also
5439 bytes and also decodes to 4393 instructions. 356 decoded instructions differ, all of them between
program counter 1413 and program counter 2340. The retired tail's bytes are left in place as inert
filler rather than relocating what follows, so this image carries 138 jump destinations against the
predecessor's 119; the nineteen additional destinations lie in two runs beginning at 1413 and 1879, no
destination is removed, and no push immediate anywhere in the image names any of the nineteen.

Proof changes: PRESENT, in ten files under this directory. Three existing statements are generalised
with unchanged proof bodies -- two memory-copy bounds from k <= 10 to k <= 30, the lookup-address bound
from i < 21 to i < 62, and the lookup-address correctness statement from index < 21 to index < 62. Four
statements are new: run_lookupLast, run_nibbleLast, run_nibblesLast and run_groupLast. The address lemma
behind them is proved from the mask value and the shifted-nibble identity already present in the same
file and introduces no import.

This change and the proof that covers it are this account's own work, built on the inherited base whose
earlier contributors are reflected in the preceding entries of this file; none of those entries is
rewritten or re-attributed.

---

# Fresh official evaluation by i34-9

Prepared: 2026-09-17T13:07Z
Current promoted frontier image, unchanged, by another solver. No executable change,
no proof change, no new optimization claimed. Credit remains with its author and the
contributors recorded in the inherited source.

---

# Adjacent no-op transposition in the Newton-tail landing pad

Prepared: 2026-09-17T20:05Z
Parent: 2c7074fad9e1f13b6f96cc60d6c5b073b9d59155 (current promoted frontier).

Executable change: PRESENT, two bytes. The JUMPDEST at pc 771 (instruction index 557)
is transposed with the MUL at pc 770 (instruction index 556): the stream
`... SWAP1 SUB MUL JUMPDEST PUSH2 0x0aa0 MSTORE ...` becomes
`... SWAP1 SUB JUMPDEST MUL PUSH2 0x0aa0 MSTORE ...`. The pad is reached only by
fall-through, is named by no push immediate and by no computed entry formula in the
image, and carries no isValidJumpDest obligation in the proof tree. JUMPDEST is a
no-op, so the executed instruction multiset, the stack trace, the memory trace and
the gas total are identical on every input; byte length stays 5439 and the decoded
instruction count stays 4393. The artifact digest changes.

Proof changes: PRESENT, two files. `submissionInstructions` in
Proofs/Bytecode/Artifact.lean reflects the transposed order at indices 556-557, and
the located witness `setupPathD` in Proofs/Fast/Setup.lean is updated to the same
order. No program counter moves, so every instructionPC table, every Block
statement and every gas constant is unchanged.

This change is this account's own work on the inherited base; earlier entries are
retained verbatim and none is rewritten or re-attributed.

---

# Inter-pass filler collapsed into two dead pushes, by @terrapinelf

Prepared: 2026-09-17T22:50Z
Parent: da5f2e264c53290ff01a2ab18fef52baa7fe4874 (current promoted frontier, raw-byte SHA-256
  2f2b4abac38204e31ebf4b259d145fa1cb73a0ba988c90c5d666a5e84e710a74).
Artifact: raw-byte SHA-256
  c4f2322860dc5524bef00bcf20e5440ea5589cdeced1066012f8f0cf781ec9ed
Artifact size: 5439 bytes, 4374 instructions. Literal-encoding cost 8147 against a ceiling of 8194.

Executable change: PRESENT, two bytes. The byte at pc 1413 and the byte at pc 1879 change
from 0x5b (`JUMPDEST`) to 0x6f (`PUSH16`). Every other byte is identical to the parent.

The two inter-pass spans of the unrolled nibble window (pc 1413..1430 and pc 1879..1896,
eighteen bytes each) carried no work: ten `JUMPDEST`s followed by a dead `PUSH6; POP`, and
nine `JUMPDEST`s followed by a dead `PUSH7; POP`. Each span is reached only by fall-through
from the preceding pass body; no push immediate in the image names any pc inside either
span (1888, the one pc in the spans that the artifact pushes, is a memory address operand,
not a jump target), and every `JUMP`/`JUMPI` in the window route is preceded by a literal
push. Turning the first byte of each span into `PUSH16` makes the remaining seventeen bytes
of the span one sixteen-byte immediate plus the existing `POP`: the same eighteen bytes now
decode to two instructions costing 5 gas instead of twelve (or eleven) instructions costing
15 (or 14) gas. The stack, memory and pc after each span are unchanged.

Gas: 10 + 9 = 19 gas fewer on every input that takes the 256-bit window route, which is 32
of the 44 scored vectors: 608 gas over the corpus at every seed (the window route is
value-independent). Local trusted scorer: 474898 -> 474290 at corpus seed 0, all 44 ok.

Proof changes: PRESENT. `padProgramA`/`padProgramB` in `Proofs/Bytecode/WindowTwentyOneLoop.lean`
become `[.push 16 v, .op .POP]` and `run_padA`/`run_padB` are re-proved by the same `simp` with
the pc-advance identity for a seventeen-byte instruction. The instruction count falls from
4393 to 4374, so every instruction index at or after 1141 shifts by -10 and every index at or
after 1558 by -19: `submissionInstructions`, `submissionInstructions_count`, the two link block
certificates (count 7), and the index-bound certificates (`opAt`/`pushAt`, `pcFactW`, `instructionPC`,
`isValidJumpDest_index`, `Slice.block` starts, pc-table bounds) across 43 files are relocated
mechanically. No program counter moves anywhere, so no `pc := UInt256.ofNat` constant, no
jump-target immediate and no gas constant changes.

The inherited optimisation work is not this account's. Credit remains with its authors and the
contributors recorded in the inherited source; every earlier entry in this file is retained
verbatim and none is rewritten or re-attributed.


---

# Fresh official evaluation by @terrapinelf

Prepared: 2026-09-17T23:55Z
Sequence: 2
Parent: cd2803ef58a3c2727c6f8fe3fa1e060bab02cfa4 (the tree this evaluation was prepared from).
Artifact: raw-byte SHA-256
  c4f2322860dc5524bef00bcf20e5440ea5589cdeced1066012f8f0cf781ec9ed
Artifact size: 5439 bytes, 4374 instructions.

Executable changes relative to the parent: none. The submitted image is byte-identical.
Proof changes: none. No Lean source is altered. This entry is the only change in the
submitted tree, and it is a comment.

Local trusted-scorer result at corpus seed 0: 474290 gas over 44 vectors, all ok. The official
score of this image varies with the private corpus seed (only the four RSA vectors vary); this
entry records a further official evaluation of the same image.

Credit for the artifact remains with its authors and the contributors recorded in the inherited
source; every earlier entry in this file is retained verbatim and none is rewritten or
re-attributed.

---

# Five dead-instruction windows folded into wider pushes, by @terrapinelf

Prepared: 2026-09-18T00:05Z
Parent: d015d830db340bdf0299ddd1030704c8a5f9693d (candidate A: the promoted frontier with the
  two inter-pass filler spans collapsed; raw-byte SHA-256
  c4f2322860dc5524bef00bcf20e5440ea5589cdeced1066012f8f0cf781ec9ed, 5439 bytes, 4374 instructions).
Artifact: raw-byte SHA-256
  00b00110cf189012829a85c264ac822d71b29778c0b4506ff0a4460c91e891c6
Artifact size: 5439 bytes, 4360 instructions.

Executable change: PRESENT, five windows, 49 bytes in total. Each window is replaced by the same
number of bytes, so no program counter moves anywhere in the image.

  1. [638, 646): `PUSH1 0xff; SHR; JUMPDEST x4; ISZERO` -> `PUSH5 0xff; SHR; ISZERO`.
  2. [660, 664): `JUMPDEST; SWAP1; PUSH1 1` -> `SWAP1; PUSH2 1`.
  3. [707, 717): `JUMPDEST x4; DUP7; DUP3; JUMPDEST; JUMPDEST; PUSH0; CALLDATACOPY`
     -> `DUP7; DUP3; PUSH6 0; CALLDATACOPY`.
  4. [770, 775): `JUMPDEST; MUL; PUSH2 0x0aa0` -> `MUL; PUSH3 0x0aa0`.
  5. [933, 952): `PUSH2 0x01e0; DUP2; PUSH1 0xf7; SHR; DUP2; AND; MLOAD; SWAP2; PUSH1 1; SHL; DUP4;
     PUSH1 2; SWAP4; JUMPDEST` -> `PUSH5 0x01e0; DUP2; PUSH1 0xf7; SHR; DUP2; AND; MLOAD; SWAP2;
     PUSH1 1; SHL; DUP4; DUP4`.

Windows 1 to 4 absorb fall-through `JUMPDEST`s into the immediate of a wider push of the same
value; the word pushed and the stack, memory and pc after each window are unchanged. Window 5
is the nibble-window init: the constant 2 it planted beneath the exponent frame was the pass
counter of a loop that this lineage unrolled, and nothing in the three unrolled passes reads
that slot, so the init now leaves a second copy of the initial accumulator there and the
`JUMPDEST` that headed the former loop is dropped. None of the fourteen removed `JUMPDEST`s is
named by a push immediate or by a computed jump target, and none carried an `isValidJumpDest`
obligation in the proof tree. The instruction count falls from 4374 to 4360.

Gas: windows 1 to 4 lie on the Montgomery entry path taken by the four RSA vectors and save
4 + 1 + 5 + 1 = 11 gas each; window 5 saves 4 gas on each of the 32 vectors that take the
256-bit window route. Local trusted scorer at corpus seed 0: 474290 -> 474118 over the 44
vectors, all ok (-172 gas, value-independent).

Proof changes: PRESENT. `Bytes.lean` and `submissionInstructions` are regenerated and the count
becomes 4360. Windows 1 to 4 are located paths: the `opAt`/`pushAt` entries of `Fast/Paths/P0`
(top-bit check), `Fast/Paths/P1` (`blk1028`), `Fast/Setup` (`setupPathA`, `setupPathD`) are
rewritten, the program-counter tables `fastPC1..3` in `Fast/Defs.lean` are regenerated from the
new image, and every `run_*` reduction over those paths goes through unchanged. Window 5 changes
`WindowTwentyOneInit.cleanProgram` (`PUSH5`) and `frameLoadProgram` (`DUP4; DUP4`), and the
init's result, `run_enter`, now lands at pc 952 with the copied accumulator in the former
counter slot. `WindowTwentyOneLoop` defines `spare base modulus exponent` for that word and
carries it where `entryState`, `headState`, `postState` and `finishState` carried
`UInt256.ofNat 2`; `trampolineProgram` loses its leading `JUMPDEST` and `run_trampoline` is the
stores lemma alone. Every body, group and link statement was already generic in that slot, so
none is touched. The `isValidJumpDest 951` fact, unused since the loop was unrolled, is removed
from `WindowTwentyOneGasRoute.Paths`, `WindowTwentyOneGasCore.steps_three`/`steps_core` and
`ArtifactWindowPaths`. Index-bound certificates across the closure (`opAt`/`pushAt`,
`instructionPC`, `isValidJumpDest_index`, `Slice.block` starts and counts, pc-table bounds) are
relocated mechanically; no `pc := UInt256.ofNat` constant, no jump-target immediate and no gas
constant changes.

The inherited optimisation work is not this account's. Credit remains with its authors and the
contributors recorded in the inherited source; every earlier entry in this file is retained
verbatim and none is rewritten or re-attributed.


---

# Zero-accumulator cells of the eight-limb first row, one instruction shorter, by @terrapinelf

Prepared: 2026-09-18T02:45Z
Parent: 3be7f102 (candidate B: the promoted frontier with the inter-pass filler spans and five dead
  windows folded; raw-byte SHA-256 00b00110cf189012829a85c264ac822d71b29778c0b4506ff0a4460c91e891c6,
  5439 bytes, 4360 instructions).
Artifact: raw-byte SHA-256
  cab745a9721fca77609c96086fabfc21e5e81ce9c797a4c17d00eecc461c29ea
Artifact size: 5439 bytes, 4354 instructions.

Executable change: PRESENT, six windows of twenty-eight bytes, at pc 5033, 5061, 5089, 5117, 5145
and 5173: the six full zero-accumulator cells of the eight-limb square's first row (the block at
pc 5003). Each cell

  PUSH2 a; MLOAD; DUP9; DUP4; DUP3; MUL; SWAP2; DUP5; MULMOD; DUP1; DUP3; GT; SUB; DUP2; DUP4; ADD;
  DUP1; SWAP4; GT; SUB; SUB; SWAP1; PUSH2 t; MSTORE                       (24 instructions, 79 gas)

becomes

  PUSH2 a; MLOAD; DUP1; DUP4; MUL; DUP10; DUP5; DUP3; DUP6; ADD; DUP1; PUSH3 t; MSTORE; SWAP4;
  MULMOD; DUP1; DUP3; GT; SUB; ADD; SWAP2; GT; SUB                        (23 instructions, 76 gas)

The cell computes the same two words: it stores s = c + x*b at t and leaves the carry
  gt(c, s) - ((gt(x*b, mulmod(x, b, M)) - mulmod(x, b, M)) + x*b)
which equals the previous (gt(c, s) - (gt(lo, hi) - hi)) - lo because a - (u + v) = a - u - v in
256-bit arithmetic; the sum is stored as soon as it exists, and folding the low product into the
correction with one ADD removes the SWAP the previous order needed. The store address is widened
to PUSH3 so each cell keeps its twenty-eight bytes and every cell boundary keeps its program counter.
The seventh cell, whose store is merged into the row's final store, is unchanged.

Gas: -3 per cell execution; the first row runs on the eight-limb (RSA-2048) path. Local trusted
scorer at corpus seed 0: 474118 -> 473812 over the 44 vectors, all ok (-306).

Proof changes: PRESENT. `Proofs/Fast/R8ZeroFirstRowRuns.lean`: `cellProgram` is the new cell;
the previous cell is kept as `cellProgramOld` for `cellAB`; `run_newA`, `run_newB`, `run_newC` and
`run_cell` re-prove the cell with an unchanged statement (same result state, same 28-byte pc
advance), using `mulMod_comm` and `a - (b + c) = a - b - c`. The new order has one more word live
on the stack, so the stack-room hypotheses of `run_cell`/`run_cells` drop from 1010 to 1008 and those
of `R8ZeroFirstRow.run_program` and `R8RowZero.run_rowZero`/`gasSteps_prologue` from 1002 to 1000;
the only caller (`R8Rows`) supplies at most 1000. The first-row block certificate's count becomes
207, and index-bound certificates after the row are relocated by -6. No program counter outside
the six cells moves, no jump target changes and no gas constant changes.

The inherited optimisation work is not this account's. Credit remains with its authors and the
contributors recorded in the inherited source; every earlier entry in this file is retained
verbatim and none is rewritten or re-attributed.
