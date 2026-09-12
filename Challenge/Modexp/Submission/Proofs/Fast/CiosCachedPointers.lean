import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacWords
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


/-! The concrete loop pointers select and terminate the generic MAC models. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPointers

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem l1_pointer (pa n j : Nat) (hpa : 32 ≤ pa)
    (hfit : pa + 32 * n ≤ 2912) (hj : j ≤ n) :
    (UInt256.ofNat (ptrAt (pa + 32 * n - 32) j)).toNat =
      pa - 32 + 32 * (n - j) := by
  rw [ptrAt_toNat _ _ (by omega) (by omega)]
  omega

theorem l2_pointer (n k : Nat) (hn : n ≤ 8) (hk : k + 1 ≤ n) :
    (UInt256.ofNat (ptrAt (2048 + 32 * n) k)).toNat =
      2080 + 32 * (n - 1 - k) := by
  rw [ptrAt_toNat _ _ (by omega) (by omega)]
  omega

theorem isTrue_gt (a b : UInt256) :
    UInt256.isTrue (UInt256.gt a b) ↔ b.toNat < a.toNat := by
  unfold UInt256.gt
  split <;> simp_all [UInt256.isTrue, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem l1_condition (pa n j : Nat) (hpa : 32 ≤ pa)
    (hfit : pa + 32 * n ≤ 2912) (hj : j ≤ n) :
    UInt256.isTrue (UInt256.gt (UInt256.ofNat (ptrAt (pa + 32 * n - 32) j))
      (UInt256.ofNat (pa - 32))) ↔ j < n := by
  rw [isTrue_gt, l1_pointer pa n j hpa hfit hj,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem l2_condition (n k : Nat) (hn : n ≤ 8) (hk : k + 1 ≤ n) :
    UInt256.isTrue (UInt256.gt (UInt256.ofNat (ptrAt (2048 + 32 * n) k))
      (UInt256.ofNat 2080)) ↔ k + 1 < n := by
  rw [isTrue_gt, l2_pointer n k hn hk,
    Challenge.EvmProof.Word.word_toNat_ofNat, show 2080 % 2 ^ 256 = 2080 by decide]
  omega

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPointers
