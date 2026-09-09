import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2TailWords

open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

/-- Replace a wrapped literal without unfolding word constructors in a larger proof. -/
theorem ofNat_eq_of_mod (a b : Nat) (h : a % 2^256 = b) :
    UInt256.ofNat a = UInt256.ofNat b := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, ← h, Nat.mod_mod]

/-- Keep the large fixed address outside definitional associativity reduction. -/
theorem store_address (p : Nat) :
    UInt256.ofNat (8288 + p) = UInt256.ofNat (8256 + p) + UInt256.ofNat 32 :=
  (congrArg UInt256.ofNat (Nat.add_assoc 32 8256 p)).trans
    ((Challenge.EvmProof.Word.ofNat_add_mod 32 (8256 + p)).symm.trans
      (Challenge.EvmProof.Word.word_add_comm _ _))

/-- The last modulus pointer wraps to the cached negative stride. -/
theorem next_address (p : Nat) (hbound : p = 0 ∨ 32 ≤ p) :
    (if p = 0 then negative32 else UInt256.ofNat (p - 32)) =
      negative32 + UInt256.ofNat p := by
  have hK : negative32 = UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 := by decide
  by_cases hp : p = 0
  · simp [hp, hK, Challenge.EvmProof.Word.ofNat_add_mod]
  · have hp32 : 32 ≤ p := hbound.resolve_left hp
    simp only [hp, if_false, hK, Challenge.EvmProof.Word.ofNat_add_mod]
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat]
    have hrearrange :
        115792089237316195423570985008687907853269984665640564039457584007913129639904 + p =
        2^256 + (p - 32) := by omega
    rw [hrearrange, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2TailWords
