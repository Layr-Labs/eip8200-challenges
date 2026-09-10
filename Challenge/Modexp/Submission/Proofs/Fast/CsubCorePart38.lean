import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart37

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

theorem cs_algebra (D M T P R d2 md t b F : Nat)
    (hlimb : d2 + md + b = t + R * F) (hinv : D + M = T + b * P) :
    D + d2 * P + (M + md * P) = T + t * P + F * (P * R) := by
  have h1 : D + d2 * P + (M + md * P) = D + M + (d2 + md) * P := by ring
  rw [h1, hinv]
  have h2 : T + b * P + (d2 + md) * P = T + (d2 + md + b) * P := by ring
  rw [h2, hlimb]
  ring

end Challenge.Modexp.Submission.Proofs.Fast.Csub
