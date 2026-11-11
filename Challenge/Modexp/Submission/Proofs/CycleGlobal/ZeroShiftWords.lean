import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftMath
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem shr_zero (x : UInt256) : UInt256.shiftRight x (UInt256.ofNat 0) = x := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.shiftRight_toNat x (by decide)]
  exact Nat.shiftRight_zero
@[simp] theorem shl_256 (x : UInt256) : UInt256.shiftLeft x (UInt256.ofNat 256) = UInt256.ofNat 0 := by
  unfold UInt256.shiftLeft
  rw [if_pos (by decide)]
  rfl
#print axioms shr_zero
#print axioms shl_256
end CycleSubmission.Global.ZeroShiftMath
