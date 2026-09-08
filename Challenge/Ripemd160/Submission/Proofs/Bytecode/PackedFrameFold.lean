import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSequence
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompression

set_option warningAsError true
set_option autoImplicit false

/-!
# Relating the emitted frame recurrence to the abstract packed fold

The execution proof follows `frameFrom`, whose suffix carries one group
constant for sixteen rounds.  The arithmetic proof follows `packedRounds`,
whose constant is indexed at every round.  This module identifies the two
without expanding either the schedule tables or the round arithmetic.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFrameFold

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSequence

/-- The actual packed message operand loaded by emitted round `i`. -/
def roundWord (memAt : UInt256 → UInt256) (i : Nat) : UInt256 :=
  memAt (UInt256.ofNat (16 * Crypto.Ripemd160.r[i]!)) |||
    memAt (UInt256.ofNat (16 * Crypto.Ripemd160.rP[i]! + 8))

/-- The packed constant carried through group `i / 16`. -/
def roundConstant (i : Nat) : UInt256 := packedK (i / 16)

/-- Replacing the suffix constant never changes the register tuple. -/
theorem boundaryFrame_regs (i : Nat) (f : Frame) :
    (boundaryFrame i f).regs = f.regs := by
  unfold boundaryFrame
  split
  · exact replaceK_regs _ f
  · rfl

/-- Projecting the constant after a replacement does not inspect its value. -/
theorem replaceK_constant (k : UInt256) (f : Frame) :
    (replaceK k f).suf.konst = k := rfl

/-- A machine round preserves the suffix constant. -/
theorem roundFrame_constant (memAt : UInt256 → UInt256) (i : Nat) (f : Frame) :
    (roundFrame memAt i f).suf.konst = f.suf.konst := by
  unfold roundFrame
  exact congrArg Suffix.konst (stepFrame_suffix _ _ _ _ f)

/-- With the current group constant in the suffix, `roundFrame` is exactly the
arithmetic fold's `packedStep`. -/
theorem roundFrame_regs (memAt : UInt256 → UInt256) (i : Nat) (f : Frame)
    (hk : f.suf.konst = roundConstant i) :
    (roundFrame memAt i f).regs =
      packedStep (roundWord memAt) roundConstant i f.regs := by
  unfold roundFrame packedStep
  rw [stepFrame_regs]
  rw [hk]
  unfold roundWord
  rfl

/-- The boundary operation leaves the just-computed register tuple intact. -/
theorem advanceFrame_regs (memAt : UInt256 → UInt256) (i : Nat) (f : Frame)
    (hk : f.suf.konst = roundConstant i) :
    (advanceFrame memAt i f).regs =
      packedStep (roundWord memAt) roundConstant i f.regs := by
  unfold advanceFrame
  rw [boundaryFrame_regs, roundFrame_regs memAt i f hk]

/-- Before a subsequent round, `advanceFrame` carries exactly that round's
group constant.  At a group boundary it is replaced; otherwise the quotient
`i / 16` is unchanged.  Round 80 deliberately has no such requirement. -/
theorem advanceFrame_constant (memAt : UInt256 → UInt256) (i : Nat)
    (hi : i + 1 < 80) (f : Frame)
    (hk : f.suf.konst = roundConstant i) :
    (advanceFrame memAt i f).suf.konst = roundConstant (i + 1) := by
  unfold advanceFrame boundaryFrame
  split
  · rw [replaceK_constant]
    rfl
  · rename_i hn
    have hmod : (i + 1) % 16 ≠ 0 := by
      intro hz
      exact hn ⟨hz, hi⟩
    rw [roundFrame_constant, hk]
    unfold roundConstant
    congr 1
    omega

/-- Starting at round `i`, the register component of `frameFrom` is the same
prefix fold as `packedRounds`.  The suffix-constant premise is conditional so
the final state at round 80 needs no fictitious sixth group constant. -/
theorem frameFrom_regs (memAt : UInt256 → UInt256) (g0 : Regs)
    (i n : Nat) (hbound : i + n ≤ 80) (f : Frame)
    (hregs : f.regs = packedRounds (roundWord memAt) roundConstant i g0)
    (hk : i < 80 → f.suf.konst = roundConstant i) :
    (frameFrom memAt i n f).regs =
      packedRounds (roundWord memAt) roundConstant (i + n) g0 := by
  induction n generalizing i f with
  | zero =>
      simpa only [frameFrom, Nat.add_zero] using hregs
  | succ n ih =>
      rw [frameFrom]
      have hi : i < 80 := by omega
      have hregs' :
          (advanceFrame memAt i f).regs =
            packedRounds (roundWord memAt) roundConstant (i + 1) g0 := by
        rw [advanceFrame_regs memAt i f (hk hi), hregs, packedRounds]
      have hk' : i + 1 < 80 →
          (advanceFrame memAt i f).suf.konst = roundConstant (i + 1) := by
        intro hinext
        exact advanceFrame_constant memAt i hinext f (hk hi)
      have hfold := ih (i + 1) (by omega) (advanceFrame memAt i f) hregs' hk'
      rw [show i + (n + 1) = (i + 1) + n by omega]
      exact hfold

/-- The full emitted recurrence therefore ends at the same arithmetic fold as
the packed compression model. -/
theorem frameFrom_zero_80_regs (memAt : UInt256 → UInt256) (f : Frame)
    (hk : f.suf.konst = packedK 0) :
    (frameFrom memAt 0 80 f).regs =
      packedRounds (roundWord memAt) roundConstant 80 f.regs := by
  apply frameFrom_regs memAt f.regs 0 80 (by decide) f rfl
  intro _
  simpa only [roundConstant, Nat.zero_div] using hk

#print axioms boundaryFrame_regs
#print axioms replaceK_constant
#print axioms roundFrame_constant
#print axioms roundFrame_regs
#print axioms advanceFrame_regs
#print axioms advanceFrame_constant
#print axioms frameFrom_regs
#print axioms frameFrom_zero_80_regs

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFrameFold
