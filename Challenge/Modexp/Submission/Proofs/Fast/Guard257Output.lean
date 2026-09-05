import Challenge.Modexp.Submission.Proofs.Fast.Guard257State

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Output

open EvmSemantics EvmSemantics.EVM
open Guard257State

def answer : Nat := 2 ^ 256 - 1
def b0 := Data.Bytes.natToBytesPadded (2 ^ 248 - 1) 32
def b1 := Data.Bytes.natToBytesPadded (255 * 2 ^ 248) 32
def answerChunks : ByteArray := b0 ++ b1

theorem answerPrefix_eq : answerChunks.extract 0 33 =
    Precompile.natToBytes answer 33 := by
  simp [answerChunks, b0, b1, answer,
    Precompile.natToBytes, Data.Bytes.natToBytesPadded]
  decide

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 33 =
      Precompile.natToBytes answer 33 := by
  rw [← answerPrefix_eq]
  change MachineState.readPadded
    (MachineState.writeBytes (MachineState.writeBytes ByteArray.empty b0 0) b1 32)
      0 33 = answerChunks.extract 0 33
  have h0 : b0.size = 32 := by
    simp only [b0, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have h1 : b1.size = 32 := by
    simp only [b1, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [show 32 = 0 + b0.size by omega,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  change MachineState.readPadded
    (MachineState.writeBytes ByteArray.empty answerChunks 0) 0 33 =
      answerChunks.extract 0 33
  have hc := Challenge.EvmProof.Memory.readPadded_congr
    (MachineState.writeBytes ByteArray.empty answerChunks 0) answerChunks 0 33 (by
      intro i hi
      rw [MachineState.writeBytes_getElem?_getD, if_pos]
      · simp
      · have hsize : answerChunks.size = 64 := by simp [answerChunks, h0, h1]
        omega)
  rw [hc]
  unfold MachineState.readPadded
  simp only [answerChunks, ByteArray.size_append, h0, h1]
  apply ByteArray.ext
  simp

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Output
