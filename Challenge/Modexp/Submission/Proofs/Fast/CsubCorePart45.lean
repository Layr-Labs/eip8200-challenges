import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart44

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

theorem csStep_lowValue_stable (memory : ByteArray) (n j : Nat) (hj : j < n) :
    lowValue (csStep memory n (j + 1)).memory 7168 n j =
      lowValue (csStep memory n j).memory 7168 n j := by
  apply lowValue_congr
  intro k hk
  simp only [csStep]
  exact readWord_write_disjoint _ _ _ _ (by omega)

end Challenge.Modexp.Submission.Proofs.Fast.Csub
