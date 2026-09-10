import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart36

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

theorem am_algebra (L A B P R T F xa xb c : Nat)
    (hlimb : T + R * F = xa + xb + c) (hinv : L + c * P = A + B) :
    L + T * P + F * (P * R) = A + xa * P + (B + xb * P) := by
  have h1 : L + T * P + F * (P * R) = L + (T + R * F) * P := by ring
  rw [h1, hlimb]
  have h2 : L + (xa + xb + c) * P = L + c * P + (xa * P + xb * P) := by ring
  rw [h2, hinv]
  ring

end Challenge.Modexp.Submission.Proofs.Fast.Csub
