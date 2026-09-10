import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart55

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

theorem csUse_le_one (memory : ByteArray) (n j : Nat)
    (htn : (MachineState.readWord (csStep memory n j).memory 8224).toNat ≤ 1) :
    (csUse memory n j).toNat ≤ 1 := by
  rw [csUse, Challenge.EvmProof.Word.word_toNat_lor]
  have hz : (UInt256.isZero (csStep memory n j).flag).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_isZero]
    split <;> omega
  rw [or_of_le_one htn hz]
  omega

end Challenge.Modexp.Submission.Proofs.Fast.Csub
