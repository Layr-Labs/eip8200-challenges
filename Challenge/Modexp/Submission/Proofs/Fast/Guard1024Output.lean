import Challenge.Modexp.Submission.Proofs.Fast.Guard1024State

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Challenge.Modexp.Submission.Proofs.Fast.Guard1024Output

open EvmSemantics EvmSemantics.EVM
open Guard1024State

def answer : Nat := 0x21d9b8173adcfbc08b66d78be2d7d2226da965bebb68c676de72d78fcc445847ef1012f0bdb13d7f9f972a183e60e8211019135863a5c8c4a5aebd302d9a8d6742cb04e6cc11f92524c25528642bf0de3bc16e3aac0eb16b1c9e45bc7585b3c42a89e5b54a69fdf0e1ad3241812d3449c6947263a1e6dcb942cbfeb9aeeb46bb

def b0 := Data.Bytes.natToBytesPadded 15311000363910303241540621865409679537502595890653539278795210471371740305479 32
def b1 := Data.Bytes.natToBytesPadded 108131171086235498843144070769070390205391711722934919355131028315980221287783 32
def b2 := Data.Bytes.natToBytesPadded 30211351789909815513928503188859640991933128769084385520359151767836288201668 32
def b3 := Data.Bytes.natToBytesPadded 19240783075872300903671752229116273808210541663683986574655295206487138977467 32

def answerChunks : ByteArray := b0 ++ b1 ++ b2 ++ b3

theorem answerChunks_eq : answerChunks = Precompile.natToBytes answer 128 := by
  simp [answerChunks, b0, b1, b2, b3, answer,
    Precompile.natToBytes, Data.Bytes.natToBytesPadded]
  decide

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 128 =
      Precompile.natToBytes answer 128 := by
  rw [← answerChunks_eq]
  change MachineState.readPadded
    (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes
      (MachineState.writeBytes ByteArray.empty b0 0) b1 32) b2 64) b3 96) 0 128 =
      answerChunks
  have h0 : b0.size = 32 := by
    simp only [b0, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have h1 : b1.size = 32 := by
    simp only [b1, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have h2 : b2.size = 32 := by
    simp only [b2, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have h3 : b3.size = 32 := by
    simp only [b3, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [show 32 = 0 + b0.size by omega,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show 64 = 0 + (b0 ++ b1).size by simp [h0, h1],
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show 96 = 0 + ((b0 ++ b1) ++ b2).size by simp [h0, h1, h2],
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  change MachineState.readPadded
    (MachineState.writeBytes ByteArray.empty answerChunks 0) 0 128 = answerChunks
  have hs := Challenge.EvmProof.Memory.readPadded_writeBytes_same ByteArray.empty
    answerChunks 0
  have hanswerSize : answerChunks.size = 128 := by
    simp [answerChunks, h0, h1, h2, h3]
  simpa only [hanswerSize] using hs

end Challenge.Modexp.Submission.Proofs.Fast.Guard1024Output
