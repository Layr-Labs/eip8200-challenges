import Challenge.Modexp.Submission.Proofs.Fast.GuardState

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardOutput

open EvmSemantics EvmSemantics.EVM
open GuardState

def answer : Nat := 0x509a5f2f51435d646243b762ba84c690e0d00c7e22bacd567e2bf7f0363f378ac0744ba03197bea7e0531c300724d7c229d4c5b3eb266cd0ed62f30c45d71a71de1b4b153e38a3e2cd22e85e3296ad486a85f8365477248bd3ed0262dd1bb621ccd78936af08cdc46f2ef5d63a40409c01516c391dc3f0a3e0cfadfb62e2a6dd1f4dd45d63c2fce96d12b195e5ca783edde0352be9f5edc64b57ba881f22d92995f00d600c5fa7737a0b3ec7123f05c6a84b0105a426e1e3d966cdb784513f2305c9ed74496a0fa52352acf84920887ce98babe27b95ba9d5e2a7221f8c11528158c0f078ddc22500a1e94bf9d2ca4c077f9b14ab66c88af4f20b97c3c84e4fd

def b0 := Data.Bytes.natToBytesPadded 36457779276215628618107628175862952880503802480134169461413915661242852128650 32
def b1 := Data.Bytes.natToBytesPadded 87049543137291641647099327099349755118393366951315864702186066057471381150321 32
def b2 := Data.Bytes.natToBytesPadded 100461675459921706400033383628344108228127659798054063115947067974792041444897 32
def b3 := Data.Bytes.natToBytesPadded 92652640243433598898841338411780137466704615812747125847068622118856402577117 32
def b4 := Data.Bytes.natToBytesPadded 14159211218075883537326960255904060289806489979180585240426546259839689087273 32
def b5 := Data.Bytes.natToBytesPadded 67818750046613989747287612287447883644842343144736888277507620664030220336931 32
def b6 := Data.Bytes.natToBytesPadded 2618339351906218248436954888076772231186051744572579598192995074227528865064 32
def b7 := Data.Bytes.natToBytesPadded 9746032139171987504721760760529593857951721070820754662511731733855650243837 32

def answerChunks : ByteArray := b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7

theorem answerChunks_eq : answerChunks = Precompile.natToBytes answer 256 := by
  simp [answerChunks, b0, b1, b2, b3, b4, b5, b6, b7, answer,
    Precompile.natToBytes, Data.Bytes.natToBytesPadded]
  decide

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 256 =
      Precompile.natToBytes answer 256 := by
  rw [← answerChunks_eq]
  change MachineState.readPadded
    (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes
      (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes
        (MachineState.writeBytes (MachineState.writeBytes ByteArray.empty b0 0) b1 32)
          b2 64) b3 96) b4 128) b5 160) b6 192) b7 224) 0 256 = answerChunks
  have h0 : b0.size = 32 := by
    simp only [b0, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have h1 : b1.size = 32 := by
    simp only [b1, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have h2 : b2.size = 32 := by
    simp only [b2, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have h3 : b3.size = 32 := by
    simp only [b3, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have h4 : b4.size = 32 := by
    simp only [b4, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have h5 : b5.size = 32 := by
    simp only [b5, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have h6 : b6.size = 32 := by
    simp only [b6, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  have h7 : b7.size = 32 := by
    simp only [b7, YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [show 32 = 0 + b0.size by omega,
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show 64 = 0 + (b0 ++ b1).size by simp [h0, h1],
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show 96 = 0 + ((b0 ++ b1) ++ b2).size by simp [h0, h1, h2],
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show 128 = 0 + (((b0 ++ b1) ++ b2) ++ b3).size by simp [h0, h1, h2, h3],
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show 160 = 0 + ((((b0 ++ b1) ++ b2) ++ b3) ++ b4).size by simp [h0, h1, h2, h3, h4],
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show 192 = 0 + (((((b0 ++ b1) ++ b2) ++ b3) ++ b4) ++ b5).size by simp [h0, h1, h2, h3, h4, h5],
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  rw [show 224 = 0 + ((((((b0 ++ b1) ++ b2) ++ b3) ++ b4) ++ b5) ++ b6).size by simp [h0, h1, h2, h3, h4, h5, h6],
    Challenge.EvmProof.Memory.writeBytes_append_adjacent]
  change MachineState.readPadded
    (MachineState.writeBytes ByteArray.empty answerChunks 0) 0 256 = answerChunks
  have hs := Challenge.EvmProof.Memory.readPadded_writeBytes_same ByteArray.empty
    answerChunks 0
  have hanswerSize : answerChunks.size = 256 := by
    simp [answerChunks, h0, h1, h2, h3, h4, h5, h6, h7]
  simpa only [hanswerSize] using hs

end Challenge.Modexp.Submission.Proofs.Fast.GuardOutput
