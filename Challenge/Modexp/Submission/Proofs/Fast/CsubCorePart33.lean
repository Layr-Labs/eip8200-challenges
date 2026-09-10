import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart32

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

theorem or_of_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b = max a b := by
  interval_cases a <;> interval_cases b <;> decide

end Challenge.Modexp.Submission.Proofs.Fast.Csub
