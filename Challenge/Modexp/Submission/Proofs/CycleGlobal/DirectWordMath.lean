import Challenge.EvmProof.Word
namespace CycleSubmission.Global.DirectWordMath
open EvmSemantics Challenge.EvmProof.Word
theorem eq_word (a b : UInt256) : UInt256.eq a b =
    if a = b then UInt256.ofNat 1 else UInt256.ofNat 0 := by
  unfold UInt256.eq
  by_cases h : a = b
  · subst a
    simp
  · have hn : a.toNat ≠ b.toNat := fun e => h (word_ext e)
    simp [h,hn]
theorem land_eq_zero (w : UInt256) : UInt256.land w (UInt256.ofNat 0) = UInt256.ofNat 0 := by
  apply word_ext
  simp [word_toNat_land,word_toNat_ofNat]
theorem land_eq_one (a b : UInt256) :
    UInt256.land (UInt256.eq a b) (UInt256.ofNat 1) = UInt256.eq a b := by
  simp only [eq_word]
  split <;> rfl
#print axioms eq_word
#print axioms land_eq_zero
#print axioms land_eq_one
end CycleSubmission.Global.DirectWordMath
