import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedInitialFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFrameFold

set_option warningAsError true
set_option autoImplicit false

/-!
# Final packed-frame control metadata

Round execution and constant swaps change registers and the active group
constant, but preserve every other suffix field.  Eighty phase flips restore
the even physical order, and the last active constant is group four.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFrameControl

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSequence
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFrameFold
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedInitialFrame

/-- All suffix metadata except the between-group constant. -/
def withoutConstant (sf : Suffix) : Suffix :=
  { sf with konst := UInt256.ofNat 0 }

theorem stepFrame_withoutConstant (r sl sr : Nat) (X : UInt256) (f : Frame) :
    withoutConstant (stepFrame r sl sr X f).suf = withoutConstant f.suf := by
  rw [stepFrame_suffix]

theorem replaceK_withoutConstant (k : UInt256) (f : Frame) :
    withoutConstant (replaceK k f).suf = withoutConstant f.suf := rfl

theorem boundaryFrame_withoutConstant (i : Nat) (f : Frame) :
    withoutConstant (boundaryFrame i f).suf = withoutConstant f.suf := by
  unfold boundaryFrame
  split
  · exact replaceK_withoutConstant _ f
  · rfl

theorem roundFrame_withoutConstant (memAt : UInt256 → UInt256)
    (i : Nat) (f : Frame) :
    withoutConstant (roundFrame memAt i f).suf = withoutConstant f.suf := by
  unfold roundFrame
  exact stepFrame_withoutConstant _ _ _ _ f

theorem advanceFrame_withoutConstant (memAt : UInt256 → UInt256)
    (i : Nat) (f : Frame) :
    withoutConstant (advanceFrame memAt i f).suf = withoutConstant f.suf := by
  unfold advanceFrame
  rw [boundaryFrame_withoutConstant, roundFrame_withoutConstant]

/-- Stable suffix metadata is preserved through any emitted-round prefix. -/
theorem frameFrom_withoutConstant (memAt : UInt256 → UInt256)
    (i n : Nat) (f : Frame) :
    withoutConstant (frameFrom memAt i n f).suf = withoutConstant f.suf := by
  induction n generalizing i f with
  | zero => rfl
  | succ n ih =>
      rw [frameFrom, ih, advanceFrame_withoutConstant]

/-- Tail-recursive frame execution composes at an arbitrary round split. -/
theorem frameFrom_add (memAt : UInt256 → UInt256)
    (i n m : Nat) (f : Frame) :
    frameFrom memAt i (n + m) f =
      frameFrom memAt (i + n) m (frameFrom memAt i n f) := by
  induction n generalizing i f with
  | zero => simp only [Nat.zero_add, Nat.add_zero, frameFrom]
  | succ n ih =>
      rw [Nat.succ_add, frameFrom, frameFrom]
      rw [show i + (n + 1) = (i + 1) + n by omega]
      exact ih (i + 1) (advanceFrame memAt i f)

/-- While another round remains, the frame carries that round's constant. -/
theorem frameFrom_constant (memAt : UInt256 → UInt256)
    (i n : Nat) (hbound : i + n < 80) (f : Frame)
    (hk : f.suf.konst = roundConstant i) :
    (frameFrom memAt i n f).suf.konst = roundConstant (i + n) := by
  induction n generalizing i f with
  | zero => simpa only [frameFrom, Nat.add_zero] using hk
  | succ n ih =>
      rw [frameFrom]
      have hnext : i + 1 < 80 := by omega
      have hk' := advanceFrame_constant memAt i hnext f hk
      have htail := ih (i + 1) (by omega) (advanceFrame memAt i f) hk'
      rw [show i + (n + 1) = (i + 1) + n by omega]
      exact htail

/-- The eightieth round performs no further group swap, so group four remains
the final suffix constant. -/
theorem frameFrom_zero_80_constant (memAt : UInt256 → UInt256) (f : Frame)
    (hk : f.suf.konst = packedK 0) :
    (frameFrom memAt 0 80 f).suf.konst = packedK 4 := by
  rw [show 80 = 79 + 1 by omega, frameFrom_add]
  change
    (advanceFrame memAt 79 (frameFrom memAt 0 79 f)).suf.konst = packedK 4
  have h79 :
      (frameFrom memAt 0 79 f).suf.konst = roundConstant 79 := by
    apply frameFrom_constant memAt 0 79 (by decide) f
    simpa only [roundConstant, Nat.zero_div] using hk
  unfold advanceFrame boundaryFrame
  rw [if_neg (by omega : ¬ ((79 + 1) % 16 = 0 ∧ 79 + 1 < 80))]
  change
    (roundFrame memAt 79 (frameFrom memAt 0 79 f)).suf.konst = packedK 4
  rw [roundFrame_constant, h79]
  rfl

/-- Dropping and then restoring the constant is an injective description of a
suffix. -/
theorem suffix_eq_of_withoutConstant {a b : Suffix}
    (hc : withoutConstant a = withoutConstant b)
    (hk : a.konst = b.konst) : a = b := by
  cases a
  cases b
  simp only [withoutConstant, Suffix.mk.injEq] at hc hk ⊢
  simp_all

/-- Canonical suffix after all eighty rounds. -/
def finalSuffix (ret xoff xend : UInt256) : Suffix :=
  { initialSuffix ret xoff xend with konst := packedK 4 }

/-- The full recurrence preserves all control metadata and ends on group four. -/
theorem initialFrame_finalSuffix (memAt : UInt256 → UInt256)
    (h : Compression.HashState) (ret xoff xend : UInt256) :
    (frameFrom memAt 0 80 (initialFrame h ret xoff xend)).suf =
      finalSuffix ret xoff xend := by
  apply suffix_eq_of_withoutConstant
  · rw [frameFrom_withoutConstant]
    rfl
  · exact frameFrom_zero_80_constant memAt _ (initialFrame_constant _ _ _ _)

def phaseAfter : Nat → Phase → Phase
  | 0, phase => phase
  | n + 1, phase => phaseAfter n phase.flip

theorem frameFrom_phase (memAt : UInt256 → UInt256)
    (i n : Nat) (f : Frame) :
    (frameFrom memAt i n f).phase = phaseAfter n f.phase := by
  induction n generalizing i f with
  | zero => rfl
  | succ n ih =>
      rw [frameFrom, ih, phase_advance]
      rfl

theorem initialFrame_finalPhase (memAt : UInt256 → UInt256)
    (h : Compression.HashState) (ret xoff xend : UInt256) :
    (frameFrom memAt 0 80 (initialFrame h ret xoff xend)).phase = Phase.even := by
  rw [frameFrom_phase, initialFrame_phase]
  decide

#print axioms frameFrom_withoutConstant
#print axioms frameFrom_add
#print axioms frameFrom_constant
#print axioms frameFrom_zero_80_constant
#print axioms initialFrame_finalSuffix
#print axioms frameFrom_phase
#print axioms initialFrame_finalPhase

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFrameControl
