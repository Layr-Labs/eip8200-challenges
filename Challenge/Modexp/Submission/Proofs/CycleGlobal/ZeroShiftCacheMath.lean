import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  simp [UInt256.land, UInt256.toNat, Fin.land, Nat.and_comm]
theorem packed_mask_eq (n : Nat) (k : UInt256) (hn : n = 4 ∨ n = 8) :
    UInt256.land (UInt256.ofNat 65535)
      (UInt256.shiftRight
        (UInt256.ofNat ((4079*65536)+18748) - UInt256.ofNat ((45*65536)+2006)*UInt256.ofNat n)
        (UInt256.ofNat 16 * UInt256.isZero k)) = UInt256.ofNat (head n k) := by
  rw [land_comm]
  exact packed_eq n k hn
#print axioms packed_mask_eq
end CycleSubmission.Global.ZeroShiftMath
