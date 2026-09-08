import Challenge.Modexp.Submission.Proofs.Fast.MonproCoreModel
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNCache
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNDispatchWords

set_option warningAsError true

/-! The concrete loop pointers select and terminate the generic MAC models. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNPointers

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open MonproKNDispatchWords

theorem l1_pointer (pa n j : Nat) (hpa : 32 ≤ pa)
    (hfit : pa + 32 * n ≤ 9472) (hj : j ≤ n) :
    (UInt256.ofNat (ptrAt (pa + 32 * n - 32) j)).toNat =
      pa - 32 + 32 * (n - j) := by
  rw [ptrAt_toNat _ _ (by omega) (by omega)]
  omega

theorem l2_pointer (n k : Nat) (hn : n ≤ 32) (hk : k + 1 ≤ n) :
    (UInt256.ofNat (ptrAt (8192 + 32 * n) k)).toNat =
      8224 + 32 * (n - 1 - k) := by
  rw [ptrAt_toNat _ _ (by omega) (by omega)]
  omega

theorem isTrue_gt (a b : UInt256) :
    UInt256.isTrue (UInt256.gt a b) ↔ b.toNat < a.toNat := by
  unfold UInt256.gt
  split <;> simp_all [UInt256.isTrue, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem l1_condition (pa n j : Nat) (hpa : 32 ≤ pa)
    (hfit : pa + 32 * n ≤ 9472) (hj : j ≤ n) :
    UInt256.isTrue (UInt256.gt (UInt256.ofNat (ptrAt (pa + 32 * n - 32) j))
      (UInt256.ofNat (pa - 32))) ↔ j < n := by
  rw [isTrue_gt, l1_pointer pa n j hpa hfit hj,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem l2_condition (n k : Nat) (hn : n ≤ 32) (hk : k + 1 ≤ n) :
    UInt256.isTrue (UInt256.gt (UInt256.ofNat (ptrAt (8192 + 32 * n) k))
      (UInt256.ofNat 8224)) ↔ k + 1 < n := by
  rw [isTrue_gt, l2_pointer n k hn hk,
    Challenge.EvmProof.Word.word_toNat_ofNat, show 8224 % 2 ^ 256 = 8224 by decide]
  omega

theorem l1_slot (pa n j : Nat) (hpa : 32 ≤ pa)
    (hfit : pa + 32 * n ≤ 9472) (hn : n ≤ 32) (hj : j < n) :
    UInt256.land (UInt256.ofNat 7)
      (UInt256.shiftRight
        (UInt256.ofNat (pa - 32) - UInt256.ofNat (ptrAt (pa + 32 * n - 32) j))
        (UInt256.ofNat 5)) = UInt256.ofNat (MonproKNResidue.residue (n - j)) := by
  have hp : UInt256.ofNat (ptrAt (pa + 32 * n - 32) j) =
      UInt256.ofNat (pa + 32 * (n - 1 - j)) := by
    apply Challenge.EvmProof.Word.word_ext
    rw [l1_pointer pa n j hpa hfit (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hp]
  exact l1_selector pa n j hpa hfit hn hj

theorem l2_slot (n k : Nat) (hn : n ≤ 32) (hk : k + 1 < n) :
    UInt256.land (UInt256.ofNat 7)
      (UInt256.shiftRight
        (UInt256.ofNat 8224 - UInt256.ofNat (ptrAt (8192 + 32 * n) k))
        (UInt256.ofNat 5)) = UInt256.ofNat (MonproKNResidue.residue (n - 1 - k)) := by
  have hp : UInt256.ofNat (ptrAt (8192 + 32 * n) k) =
      UInt256.ofNat (8256 + 32 * (n - 2 - k)) := by
    apply Challenge.EvmProof.Word.word_ext
    rw [l2_pointer n k hn (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [hp]
  exact l2_selector n k hn hk

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNPointers
