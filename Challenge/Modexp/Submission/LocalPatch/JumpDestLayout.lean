import EvmSemantics.EVM.Decode

set_option warningAsError true

/-!
# Complete jump-destination layout equivalence

`Decode.isValidJumpDest` scans instruction boundaries from byte zero, skipping
only PUSH immediate bytes. Therefore equality of the whole predicate needs only
three layout facts: equal code length, equal PUSH width at each reached
boundary, and equal JUMPDEST status at each such boundary.

Immediate payload bytes are otherwise unconstrained, including bytes equal to
`0x5b` inside PUSH data. The resulting theorem quantifies over every natural
number target, so it covers out-of-range destinations and bytes inside PUSH
immediates.
-/

namespace Challenge.Modexp.Submission.LocalPatch.JumpDestLayout

open EvmSemantics
open EvmSemantics.EVM

/-- Whether byte `pc`, considered as an instruction boundary, is JUMPDEST.
Using the pinned scanner itself avoids a second byte-to-opcode table. -/
def boundaryIsJumpDest (code : ByteArray) (pc : Nat) : Bool :=
  Decode.validJumpDestFrom code pc pc 1

/-- Linear executable comparison of the two boundary walks. -/
def sameShapeFrom (left right : ByteArray) : Nat → Nat → Bool
  | _, 0 => true
  | pc, fuel + 1 =>
      if pc < left.size then
        (Decode.pushDataSize left pc == Decode.pushDataSize right pc) &&
        (boundaryIsJumpDest left pc == boundaryIsJumpDest right pc) &&
        sameShapeFrom left right
          (pc + 1 + Decode.pushDataSize left pc) fuel
      else
        true

/-- Finite mechanically-checkable certificate for complete JUMP/JUMPI target
preservation. Its boundary scan is linear in the bytecode length. -/
def check (left right : ByteArray) : Bool :=
  (left.size == right.size) &&
    sameShapeFrom left right 0 (left.size + 1)

private theorem sameShapeFrom_refl (code : ByteArray) :
    ∀ fuel pc, sameShapeFrom code code pc fuel = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro pc
      rfl
  | succ fuel ih =>
      intro pc
      by_cases hpc : pc < code.size
      · simp [sameShapeFrom, hpc, ih]
      · simp [sameShapeFrom, hpc]

@[simp] theorem check_refl (code : ByteArray) : check code code = true := by
  simp [check, sameShapeFrom_refl]

private theorem validJumpDestFrom_eq_of_shape
    (left right : ByteArray) (target : Nat)
    (hsize : left.size = right.size) :
    ∀ fuel pc,
      sameShapeFrom left right pc fuel = true →
      Decode.validJumpDestFrom left target pc fuel =
        Decode.validJumpDestFrom right target pc fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro pc hshape
      rfl
  | succ fuel ih =>
      intro pc hshape
      by_cases hpc : pc < left.size
      · have hpcRight : pc < right.size := by omega
        simp only [sameShapeFrom, if_pos hpc, Bool.and_eq_true,
          beq_iff_eq] at hshape
        rcases hshape with ⟨⟨hpush, hboundary⟩, hnext⟩
        by_cases htarget : pc = target
        · subst target
          simpa [Decode.validJumpDestFrom, boundaryIsJumpDest,
            hpc, hpcRight] using hboundary
        · have hstopEq :
              (pc > target ∨ pc ≥ left.size) ↔
                (pc > target ∨ pc ≥ right.size) := by
            omega
          by_cases hstop : pc > target ∨ pc ≥ left.size
          · have hstopRight : pc > target ∨ pc ≥ right.size :=
              hstopEq.mp hstop
            simp [Decode.validJumpDestFrom, htarget, hstop, hstopRight]
          · have hstopRight : ¬(pc > target ∨ pc ≥ right.size) := by
              intro hr
              exact hstop (hstopEq.mpr hr)
            have hrec := ih
              (pc + 1 + Decode.pushDataSize left pc) hnext
            simpa [Decode.validJumpDestFrom, htarget, hstop,
              hstopRight, hpush] using hrec
      · have hpcRight : ¬pc < right.size := by omega
        have hgeLeft : pc ≥ left.size := Nat.le_of_not_gt hpc
        have hgeRight : pc ≥ right.size := Nat.le_of_not_gt hpcRight
        by_cases htarget : pc = target
        · subst target
          simp [Decode.validJumpDestFrom, hpc, hpcRight]
        · have hstopLeft : pc > target ∨ pc ≥ left.size := Or.inr hgeLeft
          have hstopRight : pc > target ∨ pc ≥ right.size := Or.inr hgeRight
          simp [Decode.validJumpDestFrom, htarget, hstopLeft, hstopRight]

/-- Main reusable theorem: a successful finite layout check preserves the full
`isValidJumpDest` function at every natural-number destination. -/
theorem isValidJumpDest_eq_of_check {left right : ByteArray}
    (hcheck : check left right = true) (target : Nat) :
    Decode.isValidJumpDest left target =
      Decode.isValidJumpDest right target := by
  simp only [check, Bool.and_eq_true, beq_iff_eq] at hcheck
  rcases hcheck with ⟨hsize, hshape⟩
  unfold Decode.isValidJumpDest
  have h := validJumpDestFrom_eq_of_shape left right target hsize
    (left.size + 1) 0 hshape
  simpa [hsize] using h

/-- Convenience direction used by a transported successful JUMP/JUMPI rule. -/
theorem valid_of_check {left right : ByteArray}
    (hcheck : check left right = true) {target : Nat}
    (hvalid : Decode.isValidJumpDest left target = true) :
    Decode.isValidJumpDest right target = true := by
  rw [← isValidJumpDest_eq_of_check hcheck target]
  exact hvalid

/-- Convenience direction used by exceptional/bad-jump transport. -/
theorem invalid_of_check {left right : ByteArray}
    (hcheck : check left right = true) {target : Nat}
    (hinvalid : Decode.isValidJumpDest left target = false) :
    Decode.isValidJumpDest right target = false := by
  rw [← isValidJumpDest_eq_of_check hcheck target]
  exact hinvalid

end Challenge.Modexp.Submission.LocalPatch.JumpDestLayout
