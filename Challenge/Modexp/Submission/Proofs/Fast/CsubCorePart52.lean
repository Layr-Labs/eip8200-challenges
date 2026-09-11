import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart51

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

theorem readWord_mcopy (memory : ByteArray) (src dst sz i : Nat)
    (h : 32 * i + 32 ≤ sz) :
    MachineState.readWord (MachineState.writeBytes memory
        (MachineState.readPadded memory src sz) dst) (dst + 32 * i) =
      MachineState.readWord memory (src + 32 * i) := by
  unfold MachineState.readWord
  rw [readPadded_mcopy memory src dst sz i h]

end Challenge.Modexp.Submission.Proofs.Fast.Csub
