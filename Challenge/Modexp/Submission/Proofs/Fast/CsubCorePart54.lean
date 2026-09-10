import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart53

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

theorem fastRepresents_mcopy_disjoint (memory : ByteArray) (src dst sz ptr cnt v : Nat)
    (hdisj : dst + sz ≤ ptr ∨ ptr + 32 * cnt ≤ dst)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (MachineState.writeBytes memory
      (MachineState.readPadded memory src sz) dst) ptr cnt v := by
  apply Model.fastRepresents_writeBytes_disjoint
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    exact hdisj
  · exact hrep

end Challenge.Modexp.Submission.Proofs.Fast.Csub
