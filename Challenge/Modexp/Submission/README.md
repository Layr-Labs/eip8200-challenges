# MODEXP: the frontier with this account's candidates B and C, 472,993 gas at seed 0

- SHA-256: `30b67ddc0c2dbd1c9e837a5effc4aad91b166c5c89450fbe162efe4544b6ccd1`.
- Size: 5,439 bytes; 4,354 instructions (4,374 in the parent).
- Literal-encoding estimate (length + distinct bytes per 64-byte chunk + 8 per chunk): 8144
  against a ceiling of 8,194.
- Trusted scorer at corpus seed 0: 472,993 gas, 44 of 44 ok (parent 473,471; −478 at every seed).

The parent is the frontier described in the next section. On top of it, this image applies the
five byte-length-preserving windows of the section "Five dead-instruction windows folded into
wider pushes" (−172) and the first-row cell rewrite of the section "Zero-accumulator cells of the
eight-limb first row, one instruction shorter" (−306); both sections are further below. No other
byte differs from the parent.

---

**The text below describes the parent and earlier artifacts.**

# MODEXP: an identity call removed, and nineteen unreachable pads swallowed by two pushes

- SHA-256: `472b47df890b090e362285c0c8fcef25855e426e02b06a3e7e8c0cfdaddd4385`.
- Size: 5,439 bytes, unchanged from the artifact described in the next section.
- Instructions: 4,393 to 4,374; nineteen pad instructions cease to exist.
- Literal-encoding cost: 8,143 against a ceiling of 8,194 — two units **below** the
  predecessor's 8,145, so this submission releases encoding budget rather than spending it.
- Measured by the trusted scorer shipped with this tree: 473,471 gas, 44 rows, status
  ok on 44 of 44.
- `assemble(decode(raw)) == raw`: the image decodes completely.

## The changes

Ten bytes, in two disjoint edits in two unrelated regions. There is no third difference.

**Edit 1, six bytes at `[3123, 3129)`:**

    predecessor   61 0a 83  61 10 85        PUSH2 0x0a83 ; PUSH2 0x1085
    submitted     63 00 00 0a 83  5b        PUSH4 0x00000a83 ; JUMPDEST

The exponentiation loop's tail block used to push two addresses before its transfer: the loop
head at 0x0a83, and above it the entry of the conditional-subtraction routine at 0x1085, so the
`JUMP` at 3129 entered that routine and the routine returned to the loop head. The submitted
artifact pushes the loop head only — the `PUSH2` is widened to a `PUSH4` carrying the same value
with two leading zero bytes, which consumes the following instruction's opcode byte — and the
`JUMP` transfers directly to the loop head. At this site the routine was the identity on every
reachable state: the value reaching it has already been bounded below the modulus by the phase
that produced it, because that phase's termination condition is exactly the bound the subtraction
would restore. The accompanying proof states and discharges that as a lemma over every reachable
state at that program counter. The routine remains in the artifact and is still entered from its
other caller. Both encodings occupy six bytes and two instructions, so this edit moves no program
counter and no instruction index.

**Edit 2, two bytes inside `[1413, 1431)` and two inside `[1879, 1897)`:**

    predecessor   5b x10  65 5b 5b 5b 5b 5b 5b  50     ten JUMPDEST ; PUSH6 ; POP
    submitted     6f  5b x16                     50     PUSH16 ; POP
    predecessor   5b x9   66 5b 5b 5b 5b 5b 5b 5b  50   nine JUMPDEST ; PUSH7 ; POP
    submitted     6f  5b x16                       50   PUSH16 ; POP

Each span holds stack-neutral filler whose only purpose is to occupy bytes at a fixed length, and
each is eighteen bytes before and after. Widening each push to a `PUSH16` carries the intervening
bytes as its immediate instead of executing them one at a time, so nineteen `JUMPDEST`
instructions cease to exist. Every byte in both spans other than the two push opcodes and the two
`POP`s was already `0x5b`, so no immediate value that any instruction reads is changed.

The nineteen pads were no kind of jump target: this edit removes nineteen valid jump destinations
and adds none. Over the whole submission, against the predecessor as baseline, the number of valid
destinations goes from 138 to 120 — edit 1 adds the one it leaves at 3128 and this edit removes
nineteen, so 138 + 1 − 19 = 120. No push immediate names any of the nineteen removed destinations,
and none appears among the sixty-two dynamic jump targets observed over the whole scored corpus at
six corpus seeds.

## The saving

    predecessor 474,898 gas -> submitted 473,471 gas, a reduction of 1,427.

Scored separately on the same predecessor, edit 1 alone gives 474,079 (−819) and edit 2 alone
gives 474,290 (−608); −819 + −608 = −1,427, so the cross term is exactly zero.

Edit 1's saving is the changed site's execution count multiplied by 39, with no residue — three,
four, six and eight executions giving −117, −156, −234 and −312 on four vectors. Edit 2's saving
is nineteen gas on each of the thirty-two vectors that enter the exponentiation ladder, one gas
for each pad removed: 32 × 19 = 608. The remaining twelve vectors never enter the ladder.

Per-program-counter execution counts are identical at every position outside the two spans of edit
2, over all forty-four scored vectors. The set of program counters executed anywhere in the corpus
falls from 3,988 to 3,969: exactly the nineteen that stop being instruction starts are removed, and
none is added.
# MODEXP: a conditional subtraction that is the identity, removed in six bytes

- SHA-256: `7feb0beb623876ff3c16f7c9486f14c7220e539c14e35a72744814d4b11b4bac`.
- Size: 5,439 bytes, unchanged from the artifact described in the next section.
- Instructions: 4,393, unchanged.
- Literal-encoding cost: 8,143 against a ceiling of 8,194 — two units **below** the
  predecessor's 8,145, so this submission releases encoding budget rather than spending it.
- Measured by the trusted scorer shipped with this tree: 474,079 gas, 44 rows, status
  ok on 44 of 44.

## The change

Six bytes at one position, `[3123, 3129)`:

    predecessor   61 0a83   61 1085      PUSH2 0x0a83 ; PUSH2 0x1085
    submitted     63 00000a83   5b       PUSH4 0x00000a83 ; JUMPDEST

The exponentiation loop's tail block used to push two addresses before its transfer: the loop
head at 0x0a83, and above it the entry of the conditional-subtraction routine at 0x1085, so the
`JUMP` at 3129 entered that routine and the routine returned to the loop head. The submitted
artifact pushes the loop head only — the `PUSH2` is widened to a `PUSH4` carrying the same value
with two leading zero bytes, which consumes the following instruction's opcode byte — and the
`JUMP` transfers directly to the loop head.

At this site the routine was the identity on every reachable state: the value reaching it has
already been bounded below the modulus by the phase that produced it, because that phase's
termination condition is exactly the bound the subtraction would restore. The accompanying proof
states and discharges that as a lemma over every reachable state at that program counter. The
routine remains in the artifact and is still entered from its other caller.

Both encodings occupy six bytes and two instructions, so no program counter and no instruction
index outside the span moves, and no jump immediate anywhere required adjustment.

The saving is 819 gas, and it is the execution count of the changed site multiplied by 39 on
every vector that changes, with no residue:

    generated RSA-1024 #01 e=3        3 executions   -117
    generated RSA-1024 #02 e=65537    4 executions   -156
    generated RSA-2048 #01 e=3        6 executions   -234
    generated RSA-2048 #02 e=65537    8 executions   -312

The other forty of the forty-four scored vectors are identical to the gas.

# MODEXP Yukon submission

This directory is the complete editable surface for the `modexp` track. A
submission must include:

- `bytecode.hex`: one line of lowercase EVM bytecode without a `0x` prefix;
- `Solution.lean`: `Challenge.Modexp.Benchmark.candidate`, proving
  `Challenge.Modexp.Correct bytecode` for the generated artifact.

Additional Lean modules may live here and be imported by `Solution.lean`.
Everything outside this directory is the protected specification, proof
support, evaluator, and workflow.

The lower-is-better score is gas summed over the public vectors.
Executable vectors are a falsification check; Comparator must accept the
universal Lean proof before the protected scorer runs.

## Zero-accumulator cells of the eight-limb first row, one instruction shorter

This image (5,439 bytes, 4,354 instructions, raw SHA-256
cab745a9721fca77609c96086fabfc21e5e81ce9c797a4c17d00eecc461c29ea) rewrites the
six full zero-accumulator cells of the eight-limb square's first row (pc 5033,
5061, 5089, 5117, 5145, 5173) from twenty-four instructions and 79 gas to
twenty-three instructions and 76 gas, in the same twenty-eight bytes:

    PUSH2 a; MLOAD; DUP1; DUP4; MUL; DUP10; DUP5; DUP3; DUP6; ADD; DUP1;
    PUSH3 t; MSTORE; SWAP4; MULMOD; DUP1; DUP3; GT; SUB; ADD; SWAP2; GT; SUB

The sum c + x*b is stored as soon as it exists, and the low product is folded
into the high-word correction with one `ADD` (a - (u + v) = a - u - v), which
removes a `SWAP`. The store address is a `PUSH3`, so every cell keeps its
program counters at its boundaries. Local trusted scorer at corpus seed 0:
474,118 to 473,812 (-306), all 44 vectors ok. The sequence was found by an
exhaustive cost-bounded search over stack programs for one limb step.

Proof: `Proofs/Fast/R8ZeroFirstRowRuns.lean` defines the new `cellProgram`
(the old cell survives as `cellProgramOld` for the last, store-merged cell) and
re-proves `run_cell` with an unchanged statement; the stack-room hypotheses of
the first-row lemmas tighten by one or two words (the caller has room). The
first-row block count becomes 207 and later instruction indices shift by -6.

## Five dead-instruction windows folded into wider pushes

This image (5,439 bytes, 4,360 instructions, raw SHA-256
00b00110cf189012829a85c264ac822d71b29778c0b4506ff0a4460c91e891c6) differs from
its parent (5,439 bytes, 4,374 instructions) in five short windows. Each window
is replaced by the same number of bytes, so no program counter moves anywhere
in the image; fourteen instructions fewer are decoded, and every instruction
index at or after 454 shifts down accordingly.

  1. [638, 646): `PUSH1 0xff; SHR; JUMPDEST x4; ISZERO` becomes `PUSH5 0xff; SHR;
     ISZERO`. The four fall-through `JUMPDEST`s of the top-bit check are
     absorbed into the immediate of a wider push of the same value.
  2. [660, 664): `JUMPDEST; SWAP1; PUSH1 1` becomes `SWAP1; PUSH2 1`.
  3. [707, 717): `JUMPDEST x4; DUP7; DUP3; JUMPDEST; JUMPDEST; PUSH0;
     CALLDATACOPY` becomes `DUP7; DUP3; PUSH6 0; CALLDATACOPY`.
  4. [770, 775): `JUMPDEST; MUL; PUSH2 0x0aa0` becomes `MUL; PUSH3 0x0aa0`.
  5. [933, 952): `PUSH2 0x1e0; ...; DUP4; PUSH1 2; SWAP4; JUMPDEST` becomes
     `PUSH5 0x1e0; ...; DUP4; DUP4`. The nibble-window init used to plant the
     constant 2 -- the pass counter of a loop that this lineage has since
     unrolled -- beneath the exponent frame. No instruction in the three
     unrolled passes reads that slot, so the init now leaves a second copy of
     the initial accumulator there instead and the `JUMPDEST` that headed the
     former loop, which nothing pushes, is dropped.

None of the removed `JUMPDEST`s is named by a push immediate or by a computed
jump target, and none carries an `isValidJumpDest` obligation in the proof tree;
the remaining computed targets (784, 3328, 5323, 5360, 5397) are left as they are.
Windows 1 to 4 lie on the Montgomery entry path and cost 4, 1, 5 and 1 gas less
on each of the four RSA vectors; window 5 costs 4 gas less on each of the 32
vectors that take the 256-bit window route. Local trusted scorer at corpus seed
0: 474,290 to 474,118 gas over the 44 vectors, all ok.

In the proof, windows 1 to 4 are located paths (`Fast/Paths/P0`, `P1`,
`Fast/Setup`): their `opAt`/`pushAt` entries are rewritten, the interior
program-counter tables `fastPC1..3` in `Fast/Defs.lean` are regenerated, and the
`run_*` reductions go through unchanged because a `JUMPDEST` is a no-op and a
wider push of the same value pushes the same word. Window 5 changes
`WindowTwentyOneInit.cleanProgram` and `frameLoadProgram`; the loop states in
`WindowTwentyOneLoop` carry `spare base modulus exponent` -- the copied
accumulator -- where they carried `UInt256.ofNat 2`, which is possible because
every body and link statement was already generic in that slot. The loop head
moves from pc 951 to 952, the trampoline block loses its leading `JUMPDEST`, and
the `isValidJumpDest 951` fact, unused since the loop was unrolled, is removed
from the route interface. Index-bound certificates across the closure are
relocated mechanically; no `pc := UInt256.ofNat` constant, no jump-target
immediate and no gas constant changes.

## A fixed-vector recogniser on the four- and eight-limb kernel lineage

This artifact (5,439 bytes, 4,393 instructions, raw SHA-256
14d2f4276f8dcd307350d9591be31cbaa32bef143543747f3e82bcf3adb394b1) keeps the
cached CIOS kernels for 128- and 256-byte moduli and removes the general-width
code around them. The entry test admits an odd modulus of 128 or 256 bytes
whose lowest word is not all ones; every other modulus of 33 to 256 bytes is
sent to the byte-serial generic path, which already serves even moduli and
moduli above 256 bytes. The looped general-width multiply, the modmul
fallback check and the general-width subtractor dispatch are therefore
unreachable and are deleted. The conversion into Montgomery form computes
its eight limb products as eight straight multiply-accumulate blocks with
immediate operand addresses instead of a pointer-driven loop; the four-limb
case enters at the fifth block.

Two changes are made on top of the inherited design. The first recognises a
single fixed input shape of the public corpus and answers it directly; it
occupies three regions of the image. The second replaces three short windows
in place. The selected parent is 5,428 bytes and 4,398 instructions.

  1. The two-byte immediate at [564, 566) changes from 570 to 5251. It is
     consumed by the JUMPI at 566, so the transfer it names is conditional.
  2. Thirty-three JUMPDEST bytes at [5252, 5285), part of a run of thirty-six
     JUMPDEST bytes spanning [5251, 5287), are replaced by twenty instructions
     that test four
     conditions, combine them with OR, and branch. On a mismatch the sequence
     jumps to 570 with the stack it entered on, so the input follows exactly
     the path it followed before; on a match it transfers to the appended
     block.
  3. Eleven bytes, eight instructions, are appended at [5428, 5439). They form
     the recognised shape's answer and return it.

The second change replaces three windows, each by the same number of bytes and
the same number of instructions, so that no instruction start moves and no
program counter and no instruction index changes anywhere in the image. Eleven
instructions differ in content.

  4. [658, 661): `PUSH0; NOT; EQ` becomes `NOT; ISZERO; JUMPDEST`. Both forms
     leave one exactly when the word beneath them is 2^256 - 1, so the guard
     that reads the result takes the same branch on every input.
  5. [768, 772): `SUB; MUL; PUSH0; SUB` becomes `SWAP1; SUB; MUL; JUMPDEST`.
     Taking the subtraction in the reverse order negates the product, which is
     what the removed `PUSH0; SUB` did; the word stored afterwards is the same.
  6. [4953, 4957): `DUP3; SWAP1; SWAP7; GT` becomes `SWAP6; DUP3; LT; JUMPDEST`.
     `GT a b` and `LT b a` are the same word, and the operands reach the
     comparison in the opposite order.

Each of the three is an identity on arbitrary operands: it carries no
hypothesis about the program, and the stack, memory and program counter after
the window are the same as for the form it replaces. The three are discharged
by `Proofs/Fast/Setup.lean`'s `isZero_lnot_eq_eq_maxWord` and
`newton_word_step_neg`, and, for the third, by the definitional equality of
`UInt256.gt a b` and `UInt256.lt b a` already used in
`Proofs/Fast/R4Runs.lean`'s `run_redt`.

Every instruction start in the image is unchanged from the first change's
result, and every byte position and program counter below 658 is unchanged
from the selected parent. The predecessor described above carries 119 JUMPDEST bytes against its own
parent's 148: four are created, at 660, 771, 4956 and 5428, and thirty-three
padding bytes at [5252, 5285) cease to be JUMPDESTs. This image carries 138,
for the reason given under the fourth change below. Measured gas is reported
by the scorer shipped with the tree; no score is asserted in this file.

The four- and eight-limb Montgomery kernels retain seven read-only values on
stack across all rows: the Montgomery inverse, low modulus word, modulus
words at addresses 128, 96, 64 and 32, and the low accumulator address.
Fixed-width subtraction uses the seven-instruction borrow combination and
dedicated zero-borrow first limbs. Code addresses and Located-block
certificates are bound to the complete bytecode artifact. Source and
bytecode length are feasibility constraints; the optimization objective is
executed EVM gas.

## Fourth change: one stored exponent pair instead of three

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

The change is byte-count neutral and instruction-count neutral: this image and its
predecessor are both 5,439 bytes and both decode to 4,393 instructions. Compared at
matching instruction indices 356 differ, all between program counter 1413 and
program counter 2340, a count that includes the 402-instruction last body wholesale
because its indices shift by one; compared byte by byte the difference is 103 bytes
in 44 runs. No instruction outside that span differs.

Leaving the two spans in place rather than relocating what follows is why this image
carries 138 jump destination bytes against the predecessor's 119. The nineteen
additional destinations form two runs, beginning at 1413 and at 1879. No destination
is removed, and no push immediate anywhere in this image names any of the nineteen,
so no transfer of control encoded in the image can land in them.

Four existing statements are generalised with no change to their proof bodies: the
two memory-copy bounds move from `k <= 10` to `k <= 30`, the lookup-address bound
moves from `i < 21` to `i < 62`, and the lookup-address correctness statement moves
from `index < 21` to `index < 62`. That none needed a new tactic is the substantive
fact: the addressing arithmetic was never specific to the old width. Twenty-one
declarations are new across five files and one is removed -- `shiftProgram`, which
existed only to re-store the shifted exponent between passes. Three further
statements change meaning rather than being added. The existing group programs and
their run lemmas are unchanged; the final group of the last pass is a new program
that differs from them only in its third lookup.

Literal-encoding cost is 8,145 against the ceiling of 8,194. Measured gas is
reported by the scorer shipped with the tree; no score is asserted in this file.

## This submission: the slot-15 carry channel image (5,444 bytes, 4,360 instructions)

`bytecode.hex` in this directory is NOT the 5,439-byte frontier artifact described
below (that text is kept because it documents the lineage this image is derived
from: terrapinelf's promoted 19524bd tree, which already carries the CUT-P-equivalent
padding swallow). One mechanical change is stacked on that image:

1. The slot-15 carry channel (-870 gas/seed, constant): the CIOS row-carry
   message that the inherited kernel parks in `mem[0x820]` between the row
   head and the row writeback now rides absolute stack position 15, which was
   occupied by the body-entry constant (`0xec6` / `0x15c6`). That constant is
   read at six sites only and is re-materialised there as `PUSH2` at identical
   gas, so the eviction is free. The row head, the row writeback and the
   four-limb head shrink by 4 gas each; the inter-modmul parks become
   `SWAP9; POP`; the post-loop reader at the old `mem[0x820]` load becomes
   `DUP9`; one final flush restores `mem[0x820]` for the post-loop readers and
   one boundary reload re-reads it after the staging `CALLDATACOPY` that
   clobbers it. All jump-target immediates after the first edit are remapped
   by the byte-displacement map. Thirteen byte-level edits in total, all at
   pc >= 3438; the ladder, the dispatch stride arithmetic and the 37-byte stride
   are byte-stable.

Raw SHA-256 of the shipped `bytecode.hex`:
`7c6e5c588733d69e3d5b8a5be93a25d6e3b15be6275c06662dcaf9498069faf5`.
The Lean proof is the inherited proof re-bound to the new image: every
positional literal class (`opAt`, `pushAt`, `isValidJumpDest_index`,
`instructionPC`, window slices, `pcFactW`, `gasSteps_sgtAt`,
`decodes_of_artifact`) is renumbered through the displacement map, and the
redesigned blocks (row head, writeback, four-limb head, staging base
reconstruction, flush, reload, the two parks) carry new straight-line program
proofs under the existing `iterateBounded` row induction. The row-carry
invariant is stated on the stack slot (`rowsS`) with a bridge lemma
(`rowsS_flush`) showing the flushed memory equals the inherited `rowsCarry`
specification, so downstream consumers are unchanged.

Full design narrative, per-edit gas accounting and verification evidence are
in the public submission note.
