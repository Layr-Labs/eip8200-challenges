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

## Fourth change: one addressing rule for the whole nibble window

The exponentiation core walks the exponent a nibble at a time and multiplies by
a precomputed power taken from a lookup group held in memory. In the predecessor
that group was addressed as a twenty-one entry structure, and the final nibble of
each group was served by a separate tail that re-derived its operand instead of
reading it from the frame already on hand.

This image widens the group so a single addressing rule covers the whole window
and folds the tail into that rule. The address the last nibble needs is computed
by the mask-and-shift that already existed, and the two operands it consumes are
components of the frame the enclosing program had already named. The group's
contents are unchanged, no new memory word is touched, and nothing new is written
to memory.

The change is byte-count neutral and instruction-count neutral: this image and its
predecessor are both 5,439 bytes and both decode to 4,393 instructions. 356 decoded
instructions differ, and every one lies between program counter 1413 and program
counter 2340; no instruction outside that span differs in opcode or in immediate.

Because the tail no longer re-derives what the frame already carries, the region
that implemented it is not executed. Its bytes are left in place as inert filler
rather than relocating the code that follows, which is why this image carries 138
JUMPDEST bytes against the predecessor's 119. The nineteen additional destinations
form two runs, beginning at 1413 and at 1879. No destination is removed, and no
push immediate anywhere in this image names any of the nineteen, so no transfer of
control encoded in the image can land in the filler.

Three existing statements are generalised with no change to their proof bodies:
the two memory-copy bounds move from `k <= 10` to `k <= 30`, the lookup-address
bound moves from `i < 21` to `i < 62`, and the lookup-address correctness statement
moves from `index < 21` to `index < 62`. That none needed a new tactic is the
substantive fact: the addressing arithmetic was never specific to the old width.
Four statements are new -- `run_lookupLast`, the program serving the final nibble;
`run_nibbleLast` and `run_nibblesLast`, its step and iterated step; and
`run_groupLast`, the group-level statement tying them together. The address lemma
behind them states that masking the twice-shifted exponent with 480 yields
thirty-two times the exponent's low nibble, and is proved from the numeric value
of the mask and the shifted-nibble identity already present in the same file,
introducing no import.

Literal-encoding cost is 8,145 against the ceiling of 8,194. Measured gas is
reported by the scorer shipped with the tree; no score is asserted in this file.
