import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart29

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

theorem lowValue_congr {a b : ByteArray} {ptr n j : Nat}
    (h : ∀ k, k < j → MachineState.readWord a (ptr + 32 * (n - 1 - k)) =
      MachineState.readWord b (ptr + 32 * (n - 1 - k))) :
    lowValue a ptr n j = lowValue b ptr n j := by
  unfold lowValue
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [h k (by simpa using hk)]

end Challenge.Modexp.Submission.Proofs.Fast.Csub
