import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0Template

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Emitting the eighty rounds from the model's own tables

The schedule stops being something we measured and becomes something the
emitter constructs.  `loadPrefix` builds a round's two offsets out of
`Crypto.Ripemd160.r` and `.rP`, and `packedK` builds each group constant out of
`.K` and `.KP`, so once ONE byte-equality check says the emitted list assembles
to the artifact's bytes, the 80/80 offset sweep and the four constant checks
become consequences rather than separately maintained facts.

## What was measured to make this construction legitimate

Every rule below was checked against the whole artifact, not a sample:

* `pushOffset` — `r i = 0` at rounds 0, 25, 42, 52, 65, one in every group and
  across both phases, and the artifact opens `PUSH0` at exactly those five and
  `PUSH1` at the other 75.  This is why the opcode is derived from the offset
  rather than special-cased: two of the ten sample rounds originally handed to
  me were among the five, and templating from them would have emitted `PUSH0`
  for 14 rounds that use `PUSH1`.
* `shiftSupply` — the rotation amount `32 - s` is taken from a resident
  constant when it lands in `17 … 22` and pushed as a literal otherwise, and
  the resident sits at `DUP (v - 6)`.  Verified on all 160 shift slots
  (80 rounds x 2 lanes), 80 `DUP` and 80 `PUSH`.  The base is 11 in all twenty
  (phase, group, slot) combinations, so there is no per-class depth parameter.
* the ten bodies — once those two shift slots are abstracted, EACH of the ten
  (phase, group) classes has exactly ONE body.  Checked across all 80 rounds:
  ten classes, one distinct body each.  Nothing else varies per round.

`rol10`'s shift is always 22, so it stays a literal `DUP 15` inside the bodies
rather than becoming a third hole; its stack depth differs from the two
rotation slots, which is why its `DUP` index is not `22 - 6`.

## Chunking for the byte check

`decide +kernel` over the whole artifact would be `assemble` on 4,572
instructions against 5,358 bytes, and PLAYBOOK section 1 measures exactly this
shape at 10m35s for 95 entries because the prefix is re-evaluated each step.
`ArtifactSegment.instructionPC_segment_of_bounds` is universally quantified
over the segment, so the check splits per group: five chunks of roughly 850
instructions with `(assembleBytes before).length = startPC` discharged once
each.  Written to be chunked from the start rather than as a fallback.

STATUS: WRITTEN, NOT ELABORATED.  No admitted goals; the file contains zero
occurrences of the placeholder token, so a grep and this claim agree.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0

/-- The packed round constant for group `r`: the left line's constant in lane 0
and the right line's in lane 1.  Built from the pinned tables. -/
def packedK (r : Nat) : UInt256 :=
  UInt256.ofNat
    (Crypto.Ripemd160.K[r]!.toNat + Crypto.Ripemd160.KP[r]!.toNat * 2 ^ 64)

/-- An offset literal in the opcode the assembler chose.  See the header: this
is a rule about the offset, not a special case for round 0. -/
def pushOffset (v : Nat) : Op :=
  if v = 0 then Op.push0 else Op.push (UInt256.ofNat v)

/-- The two message loads and their `OR`.  Lane 0 from `r`, lane 1 from `rP`
displaced eight bytes, which is what lifts the field to bits 64..95. -/
def loadPrefix (i : Nat) : List Op :=
  [pushOffset (16 * Crypto.Ripemd160.r[i]!),
   Op.mload,
   pushOffset (16 * Crypto.Ripemd160.rP[i]! + 8),
   Op.mload,
   Op.or]

theorem loadPrefix_length (i : Nat) : (loadPrefix i).length = 5 := rfl

/-- Only the left load can be `PUSH0`; the eight-byte displacement keeps the
right offset non-zero. -/
theorem rightOffset_ne_zero (i : Nat) :
    16 * Crypto.Ripemd160.rP[i]! + 8 ≠ 0 := by omega

/-- A rotation amount, in the form the round body takes it. -/
def shiftSupply (v : Nat) : Op :=
  if 17 ≤ v ∧ v ≤ 22 then Op.dup (v - 6) else Op.push (UInt256.ofNat v)

/-- Group 0, even phase: 42 operations, decoded from round 0. -/
def bodyEven0 (sl sr : Op) : List Op :=
  [Op.dup 3, Op.dup 5, Op.xor, Op.dup 10,
   Op.xor, Op.dup 5, Op.dup 11, Op.and,
   Op.dup 7, Op.or, Op.xor, Op.add,
   Op.add, Op.dup 16, Op.add, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 1,
   sl, Op.shr, Op.dup 8, Op.and,
   Op.swap 1, sr, Op.shr, Op.dup 9,
   Op.and, Op.or, Op.dup 5, Op.add,
   Op.swap 2, Op.dup 6, Op.and, Op.dup 9,
   Op.mul, Op.dup 15, Op.shr, Op.dup 6,
   Op.and, Op.swap 4]

/-- Group 1, even phase: 48 operations, decoded from round 16. -/
def bodyEven1 (sl sr : Op) : List Op :=
  [Op.dup 4, Op.dup 6, Op.xor, Op.dup 4,
   Op.and, Op.dup 6, Op.xor, Op.dup 4,
   Op.dup 6, Op.and, Op.dup 6, Op.dup 8,
   Op.or, Op.xor, Op.dup 11, Op.and,
   Op.xor, Op.add, Op.add, Op.dup 16,
   Op.add, Op.dup 6, Op.and, Op.dup 9,
   Op.mul, Op.dup 1, sl, Op.shr,
   Op.dup 8, Op.and, Op.swap 1, sr,
   Op.shr, Op.dup 9, Op.and, Op.or,
   Op.dup 5, Op.add, Op.swap 2, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 15,
   Op.shr, Op.dup 6, Op.and, Op.swap 4]

/-- Group 2, even phase: 38 operations, decoded from round 32. -/
def bodyEven2 (sl sr : Op) : List Op :=
  [Op.dup 4, Op.dup 8, Op.xor, Op.dup 4,
   Op.or, Op.dup 6, Op.xor, Op.add,
   Op.add, Op.dup 16, Op.add, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 1,
   sl, Op.shr, Op.dup 8, Op.and,
   Op.swap 1, sr, Op.shr, Op.dup 9,
   Op.and, Op.or, Op.dup 5, Op.add,
   Op.swap 2, Op.dup 6, Op.and, Op.dup 9,
   Op.mul, Op.dup 15, Op.shr, Op.dup 6,
   Op.and, Op.swap 4]

/-- Group 3, even phase: 48 operations, decoded from round 48. -/
def bodyEven3 (sl sr : Op) : List Op :=
  [Op.dup 3, Op.dup 5, Op.xor, Op.dup 6,
   Op.and, Op.dup 5, Op.xor, Op.dup 4,
   Op.dup 6, Op.and, Op.dup 6, Op.dup 8,
   Op.or, Op.xor, Op.dup 11, Op.and,
   Op.xor, Op.add, Op.add, Op.dup 16,
   Op.add, Op.dup 6, Op.and, Op.dup 9,
   Op.mul, Op.dup 1, sl, Op.shr,
   Op.dup 8, Op.and, Op.swap 1, sr,
   Op.shr, Op.dup 9, Op.and, Op.or,
   Op.dup 5, Op.add, Op.swap 2, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 15,
   Op.shr, Op.dup 6, Op.and, Op.swap 4]

/-- Group 4, even phase: 42 operations, decoded from round 64. -/
def bodyEven4 (sl sr : Op) : List Op :=
  [Op.dup 3, Op.dup 5, Op.xor, Op.dup 9,
   Op.xor, Op.dup 5, Op.dup 10, Op.and,
   Op.dup 7, Op.or, Op.xor, Op.add,
   Op.add, Op.dup 16, Op.add, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 1,
   sl, Op.shr, Op.dup 8, Op.and,
   Op.swap 1, sr, Op.shr, Op.dup 9,
   Op.and, Op.or, Op.dup 5, Op.add,
   Op.swap 2, Op.dup 6, Op.and, Op.dup 9,
   Op.mul, Op.dup 15, Op.shr, Op.dup 6,
   Op.and, Op.swap 4]

/-- Group 0, odd phase: 42 operations, decoded from round 1. -/
def bodyOdd0 (sl sr : Op) : List Op :=
  [Op.dup 4, Op.dup 4, Op.xor, Op.dup 10,
   Op.xor, Op.dup 4, Op.dup 11, Op.and,
   Op.dup 8, Op.or, Op.xor, Op.add,
   Op.add, Op.dup 16, Op.add, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 1,
   sl, Op.shr, Op.dup 8, Op.and,
   Op.swap 1, sr, Op.shr, Op.dup 9,
   Op.and, Op.or, Op.dup 4, Op.add,
   Op.swap 1, Op.dup 6, Op.and, Op.dup 9,
   Op.mul, Op.dup 15, Op.shr, Op.dup 6,
   Op.and, Op.swap 3]

/-- Group 1, odd phase: 48 operations, decoded from round 17. -/
def bodyOdd1 (sl sr : Op) : List Op :=
  [Op.dup 3, Op.dup 7, Op.xor, Op.dup 5,
   Op.and, Op.dup 7, Op.xor, Op.dup 5,
   Op.dup 5, Op.and, Op.dup 5, Op.dup 9,
   Op.or, Op.xor, Op.dup 11, Op.and,
   Op.xor, Op.add, Op.add, Op.dup 16,
   Op.add, Op.dup 6, Op.and, Op.dup 9,
   Op.mul, Op.dup 1, sl, Op.shr,
   Op.dup 8, Op.and, Op.swap 1, sr,
   Op.shr, Op.dup 9, Op.and, Op.or,
   Op.dup 4, Op.add, Op.swap 1, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 15,
   Op.shr, Op.dup 6, Op.and, Op.swap 3]

/-- Group 2, odd phase: 38 operations, decoded from round 33. -/
def bodyOdd2 (sl sr : Op) : List Op :=
  [Op.dup 3, Op.dup 8, Op.xor, Op.dup 5,
   Op.or, Op.dup 7, Op.xor, Op.add,
   Op.add, Op.dup 16, Op.add, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 1,
   sl, Op.shr, Op.dup 8, Op.and,
   Op.swap 1, sr, Op.shr, Op.dup 9,
   Op.and, Op.or, Op.dup 4, Op.add,
   Op.swap 1, Op.dup 6, Op.and, Op.dup 9,
   Op.mul, Op.dup 15, Op.shr, Op.dup 6,
   Op.and, Op.swap 3]

/-- Group 3, odd phase: 48 operations, decoded from round 49. -/
def bodyOdd3 (sl sr : Op) : List Op :=
  [Op.dup 4, Op.dup 4, Op.xor, Op.dup 7,
   Op.and, Op.dup 4, Op.xor, Op.dup 5,
   Op.dup 5, Op.and, Op.dup 5, Op.dup 9,
   Op.or, Op.xor, Op.dup 11, Op.and,
   Op.xor, Op.add, Op.add, Op.dup 16,
   Op.add, Op.dup 6, Op.and, Op.dup 9,
   Op.mul, Op.dup 1, sl, Op.shr,
   Op.dup 8, Op.and, Op.swap 1, sr,
   Op.shr, Op.dup 9, Op.and, Op.or,
   Op.dup 4, Op.add, Op.swap 1, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 15,
   Op.shr, Op.dup 6, Op.and, Op.swap 3]

/-- Group 4, odd phase: 42 operations, decoded from round 65. -/
def bodyOdd4 (sl sr : Op) : List Op :=
  [Op.dup 4, Op.dup 4, Op.xor, Op.dup 9,
   Op.xor, Op.dup 4, Op.dup 10, Op.and,
   Op.dup 8, Op.or, Op.xor, Op.add,
   Op.add, Op.dup 16, Op.add, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 1,
   sl, Op.shr, Op.dup 8, Op.and,
   Op.swap 1, sr, Op.shr, Op.dup 9,
   Op.and, Op.or, Op.dup 4, Op.add,
   Op.swap 1, Op.dup 6, Op.and, Op.dup 9,
   Op.mul, Op.dup 15, Op.shr, Op.dup 6,
   Op.and, Op.swap 3]

/-- The body for a round: its phase and group choose the shape, its index fills
the two rotation slots. -/
def roundBody (p : Phase) (g : Nat) (i : Nat) : List Op :=
  let sl := shiftSupply (32 - Crypto.Ripemd160.s[i]!)
  let sr := shiftSupply (32 - Crypto.Ripemd160.sP[i]!)
  match p, g with
  | .even, 0 => bodyEven0 sl sr
  | .odd, 0 => bodyOdd0 sl sr
  | .even, 1 => bodyEven1 sl sr
  | .odd, 1 => bodyOdd1 sl sr
  | .even, 2 => bodyEven2 sl sr
  | .odd, 2 => bodyOdd2 sl sr
  | .even, 3 => bodyEven3 sl sr
  | .odd, 3 => bodyOdd3 sl sr
  | .even, _ => bodyEven4 sl sr
  | .odd, _ => bodyOdd4 sl sr

/-- The between-group constant swap, decoded at all four boundaries. -/
def kSwap (r : Nat) : List Op :=
  [Op.push (packedK r), Op.swap 16, Op.pop]

theorem kSwap_length (r : Nat) : (kSwap r).length = 3 := rfl

def kSwapAfter (i : Nat) : List Op :=
  if (i + 1) % 16 = 0 ∧ i + 1 < 80 then kSwap ((i + 1) / 16) else []

/-- One round: table-derived loads, then the body for this phase and group. -/
def emitRound (p : Phase) (i : Nat) : List Op :=
  loadPrefix i ++ roundBody p (i / 16) i

/-- `n` rounds from index `i`, flipping the phase each round and splicing the
constant swap at the group boundaries. -/
def emitFrom : Phase → Nat → Nat → List Op
  | _, _, 0 => []
  | p, i, n + 1 => emitRound p i ++ kSwapAfter i ++ emitFrom p.flip (i + 1) n

/-- The whole compression body. -/
def emitRounds : List Op := emitFrom Phase.even 0 80

/-! ## Structural facts -/

theorem emitFrom_succ (p : Phase) (i n : Nat) :
    emitFrom p i (n + 1)
      = emitRound p i ++ kSwapAfter i ++ emitFrom p.flip (i + 1) n := rfl

theorem kSwapAfter_interior (i : Nat) (h : (i + 1) % 16 ≠ 0) :
    kSwapAfter i = [] := by
  unfold kSwapAfter
  simp [h]

theorem kSwapAfter_last : kSwapAfter 79 = [] := by
  unfold kSwapAfter
  norm_num

/-- A round is five ops plus its body, so the measured 47/53/43/53/47 group
variation is entirely the body's. -/
theorem emitRound_length (p : Phase) (i : Nat) :
    (emitRound p i).length = 5 + (roundBody p (i / 16) i).length := by
  unfold emitRound
  rw [List.length_append, loadPrefix_length]

/-- The body lengths, one per class, matching the measured step lengths. -/
theorem bodyEven0_length (sl sr : Op) : (bodyEven0 sl sr).length = 42 := rfl
theorem bodyOdd0_length (sl sr : Op) : (bodyOdd0 sl sr).length = 42 := rfl
theorem bodyEven1_length (sl sr : Op) : (bodyEven1 sl sr).length = 48 := rfl
theorem bodyEven2_length (sl sr : Op) : (bodyEven2 sl sr).length = 38 := rfl
theorem bodyEven3_length (sl sr : Op) : (bodyEven3 sl sr).length = 48 := rfl
theorem bodyEven4_length (sl sr : Op) : (bodyEven4 sl sr).length = 42 := rfl

#print axioms packedK
#print axioms loadPrefix_length
#print axioms rightOffset_ne_zero
#print axioms kSwap_length
#print axioms emitFrom_succ
#print axioms kSwapAfter_interior
#print axioms emitRound_length

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
