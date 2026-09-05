import Challenge.Modexp.Submission.Proofs.Fast.Guard257State
import Challenge.Modexp.Submission.Proofs.Fast.Guard257Spec

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Output

open EvmSemantics EvmSemantics.EVM
open Guard257State

def b0 := Data.Bytes.natToBytesPadded 452312848583266388373324160190187140051835877600158453279131187530910662655 32
def b1 := Data.Bytes.natToBytesPadded 115339776388732929035197660848497720713218148788040405586178452820382218977280 32

/-- The two stored words are the 33 answer bytes followed by 31 zero bytes. -/
def answerBytes : ByteArray := Precompile.natToBytes Guard257Spec.answer 33
def padBytes : ByteArray := ByteArray.mk (Array.replicate 31 0)

theorem answerChunks_eq : b0 ++ b1 = answerBytes ++ padBytes := by
  simp [b0, b1, answerBytes, padBytes, Guard257Spec.answer,
    Precompile.natToBytes, Data.Bytes.natToBytesPadded]
  decide

theorem answerBytes_size : answerBytes.size = 33 := by
  simp only [answerBytes, Precompile.natToBytes,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 33 =
      Precompile.natToBytes Guard257Spec.answer 33 := by
  change MachineState.readPadded
    (MachineState.writeBytes (MachineState.writeBytes ByteArray.empty b0 0) b1 32) 0 33 =
      answerBytes
  have h0 : b0.size = 32 := by
    simp only [b0, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [show 32 = 0 + b0.size by omega,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent, answerChunks_eq,
    ← Challenge.EvmProof.Memory.writeBytes_append_adjacent, Nat.zero_add,
    answerBytes_size]
  rw [Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint _ _ 0 33 33 (Or.inl (by omega))]
  have hs := Challenge.EvmProof.Memory.readPadded_writeBytes_same ByteArray.empty
    answerBytes 0
  simpa only [answerBytes_size] using hs

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Output
