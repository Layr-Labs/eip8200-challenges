import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart39

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

theorem amStep_lowValue_stable (memory : ByteArray) (pa pb n j : Nat) (hj : j < n) :
    lowValue (amStep memory pa pb n (j + 1)).memory 8256 n j =
      lowValue (amStep memory pa pb n j).memory 8256 n j := by
  apply lowValue_congr
  intro k hk
  simp only [amStep]
  exact readWord_write_disjoint _ _ _ _ (by omega)

end Challenge.Modexp.Submission.Proofs.Fast.Csub
