import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2State
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Output

open EvmSemantics EvmSemantics.EVM
open GuardEip2State

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = Precompile.natToBytes 0 32 := by
  have hz : ((0 : UInt256)).toNat = 0 := by decide
  have h0 : (Data.Bytes.natToBytesPadded 0 32).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size 0 32
  have hs := Challenge.EvmProof.Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded 0 32) 0
  rw [h0] at hs
  simp only [answerMemory, storeWord, hz]
  exact hs

end Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Output
