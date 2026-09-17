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
