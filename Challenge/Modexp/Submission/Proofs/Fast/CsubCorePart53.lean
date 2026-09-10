import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart52

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

theorem fastRepresents_mcopy (memory : ByteArray) (src dst n v : Nat) (_hn : 1 ≤ n)
    (hrep : Model.FastRepresents memory src n v) :
    Model.FastRepresents (MachineState.writeBytes memory
      (MachineState.readPadded memory src (32 * n)) dst) dst n v := by
  apply Model.fastRepresents_of_limbs hrep.1
  intro k hk
  rw [readWord_mcopy memory src dst (32 * n) (n - 1 - k) (by omega)]
  exact Model.readLimb_of_fastRepresents hrep hk

end Challenge.Modexp.Submission.Proofs.Fast.Csub
