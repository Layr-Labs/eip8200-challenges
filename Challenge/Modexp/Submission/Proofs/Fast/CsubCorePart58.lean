import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart57

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

theorem csSrc_toNat (memory : ByteArray) (n j : Nat)
    (huse : (csUse memory n j).toNat ≤ 1) :
    (csSrc memory n j).toNat =
      if (csUse memory n j).toNat = 0 then 8256 else 7168 := by
  have h8256 : (8256 : UInt256).toNat = 8256 := by decide
  have hL : (115792089237316195423570985008687907853269984665640564039457584007913129638848 :
      UInt256).toNat =
      115792089237316195423570985008687907853269984665640564039457584007913129638848 := by
    decide
  rw [csSrc, Challenge.EvmProof.Word.word_toNat_add, word_toNat_mul, h8256, hL]
  rcases Nat.lt_or_ge (csUse memory n j).toNat 1 with h | h
  · rw [show (csUse memory n j).toNat = 0 from by omega, if_pos rfl]
    norm_num
  · rw [show (csUse memory n j).toNat = 1 from by omega, if_neg (by norm_num)]
    norm_num

end Challenge.Modexp.Submission.Proofs.Fast.Csub
