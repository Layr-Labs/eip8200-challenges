import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart35

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

theorem readWord_write_disjoint (memory : ByteArray) (w addr wr : Nat)
    (hdisj : addr + 32 ≤ wr ∨ wr + 32 ≤ addr) :
    MachineState.readWord (MachineState.writeBytes memory
      (Data.Bytes.natToBytesPadded w 32) wr) addr =
      MachineState.readWord memory addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact hdisj

end Challenge.Modexp.Submission.Proofs.Fast.Csub
