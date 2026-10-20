import Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64Anchor
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalXorRaw

set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
# Repeat math under the full-word XOR screen

`condition input = UInt256.xor KnownInputData.fullWord (MachineState.readWord input 0)`
directly pins `referenceWord input = KnownInputData.fullWord` when `condition input = 0`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64RepeatMath

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open KnownInputCompactState
open TerminalMulRaw UnrolledRepeatRaw DirectGuard

/-- The on-chain full-word XOR screen at `PC 18..58`. -/
def condition (input : ByteArray) : UInt256 :=
  UInt256.xor KnownInputData.fullWord (MachineState.readWord input 0)

theorem condition_zero_iff (input : ByteArray) :
    condition input = 0 ↔ referenceWord input = KnownInputData.fullWord := by
  unfold condition referenceWord
  rw [KnownInputLogic.wordXor_eq_zero_iff]
  exact eq_comm

private theorem isZero_eq_one_iff (a : UInt256) : UInt256.isZero a = 1 ↔ a = 0 := by
  unfold UInt256.isZero
  split
  · rename_i h
    exact ⟨fun _ => Word.word_ext h, fun _ => rfl⟩
  · rename_i h
    refine ⟨?_, ?_⟩
    · intro h0
      exact absurd h0 (by decide : (0 : UInt256) ≠ 1)
    · intro hz
      exact absurd (congrArg UInt256.toNat hz) h

/-- Under the full-word XOR screen, a zero terminal mismatch is exactly the repeated
word together with every equality-accumulator comparison. -/
theorem mismatch_zero_iff (input : ByteArray) (hcond : condition input = 0) :
    TerminalXorRaw.mismatch input = 0 ↔
      referenceWord input = KnownInputData.fullWord ∧ equalityAcc input 10 = 1 := by
  have href : referenceWord input = KnownInputData.fullWord :=
    (condition_zero_iff input).1 hcond
  constructor
  · intro hm
    have heq : equalityAcc input 10 = 1 := by
      rw [← TerminalXorRaw.isZero_mismatch input href]
      rw [hm]
      exact (isZero_eq_one_iff 0).2 rfl
    exact ⟨href, heq⟩
  · rintro ⟨_, heq⟩
    have hzero : UInt256.isZero (TerminalXorRaw.mismatch input) = 1 := by
      rw [TerminalXorRaw.isZero_mismatch input href, heq]
    exact (isZero_eq_one_iff _).1 hzero

/-- The pinned 1000-byte vector passes the full-word screen. -/
theorem target_condition : condition KnownInputData.targetInput = 0 := by
  have hread := KnownInputData.targetInput_readWord 0 (by decide : (0 : Nat) < 32)
  have href : referenceWord KnownInputData.targetInput = KnownInputData.fullWord := by
    simpa [referenceWord, KnownInputData.expectedWord] using hread
  exact (condition_zero_iff KnownInputData.targetInput).2 href

theorem mismatch_zero_target (input : ByteArray) (hsize : input.size = 1000)
    (hcond : condition input = 0) (hm : TerminalXorRaw.mismatch input = 0) :
    input = KnownInputData.targetInput := by
  obtain ⟨href, heq⟩ := (mismatch_zero_iff input hcond).1 hm
  have hrev : reverseAcc input 10 = 0 :=
    (isZero_eq_one_iff _).1 (by rw [← equalityAcc_reverse, heq])
  exact reverseAcc_zero_target input hsize href hrev

/-- Size 1000 and the full-word screen make a zero mismatch the pinned vector. -/
theorem mismatch_zero_iff_target (input : ByteArray) (hsize : input.size = 1000)
    (hcond : condition input = 0) :
    TerminalXorRaw.mismatch input = 0 ↔ input = KnownInputData.targetInput := by
  constructor
  · exact mismatch_zero_target input hsize hcond
  · intro ht
    subst ht
    have href : referenceWord KnownInputData.targetInput = KnownInputData.fullWord := by
      have hread := KnownInputData.targetInput_readWord 0 (by decide : (0 : Nat) < 32)
      simpa [referenceWord, KnownInputData.expectedWord] using hread
    have heq : equalityAcc KnownInputData.targetInput 10 = 1 := by
      rw [equalityAcc_reverse, reverseAcc_target_zero]
      exact (isZero_eq_one_iff 0).2 rfl
    exact (mismatch_zero_iff _ hcond).2 ⟨href, heq⟩

#print axioms mismatch_zero_iff
#print axioms target_condition
#print axioms mismatch_zero_target
#print axioms mismatch_zero_iff_target

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64RepeatMath
