import Challenge.EvmProof.Word
open EvmSemantics
open Challenge.EvmProof.Word
namespace CycleSubmission.DifferenceBranch
 theorem sub_zero_eq (a b : UInt256) (h : a - b = UInt256.ofNat 0) : a = b := by
  apply word_ext
  have hv := congrArg UInt256.toNat h
  rw [word_toNat_sub_cond] at hv
  have ha : a.toNat < 2^256 := a.val.isLt
  have hb : b.toNat < 2^256 := b.val.isLt
  have hz : (UInt256.ofNat 0).toNat = 0 := rfl
  rw [hz] at hv
  split_ifs at hv <;> omega
 theorem neg_zero_of_difference_zero (a q carry : UInt256)
     (h : a - q = UInt256.ofNat 0) :
     UInt256.gt (UInt256.lt a q) carry = UInt256.ofNat 0 := by
  have he := sub_zero_eq a q h
  subst q
  simp [UInt256.lt, UInt256.gt, UInt256.toNat, UInt256.ofNat]
 theorem difference_nonzero_of_flags (a q carry : UInt256)
     (h : (UInt256.gt (UInt256.lt a q) carry).toNat ≠ 0 ∨ (a-q).toNat ≠ 0) :
     (a-q).toNat ≠ 0 := by
  rcases h with hn | ht
  · intro hz
    have he : a-q = UInt256.ofNat 0 := word_ext hz
    rw [neg_zero_of_difference_zero a q carry he] at hn
    exact hn rfl
  · exact ht
 theorem lazy_reconstruct (a q : UInt256) : q + (a-q) = a := by
  apply word_ext
  rw [word_toNat_add, word_toNat_sub_cond]
  have ha : a.toNat < 2^256 := a.val.isLt
  have hq : q.toNat < 2^256 := q.val.isLt
  split_ifs <;> omega
end CycleSubmission.DifferenceBranch
