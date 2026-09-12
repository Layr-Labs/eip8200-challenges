import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedInputData

open EvmSemantics EvmSemantics.EVM

/-- Seeded corpus vector `generated #01` from the pinned scorer. -/
def generatedInput : ByteArray := ByteArray.mk #[
  0x73, 0xdd, 0xde, 0x17, 0x0c, 0x56, 0x69, 0x6f,
  0x8b, 0xe0, 0x41, 0x7d, 0xea, 0x23, 0xe4, 0x83,
  0x5e, 0xf6, 0x31, 0xc7, 0x60, 0xbb, 0xc9, 0xfb,
  0xe9, 0x62, 0x88, 0x5a, 0xed, 0x87, 0xd4, 0x42]

/-- `RIPEMD160 generatedInput`, in the scorer's 20-byte return format. -/
def generatedDigest : ByteArray := ByteArray.mk #[
  0x97, 0x61, 0x32, 0xce, 0xa9, 0xa6, 0xad, 0x96, 0x0a, 0x57,
  0xa6, 0x5f, 0x7f, 0x0a, 0xfe, 0x0b, 0x0e, 0x3a, 0x01, 0x84]

/-- The 32-byte return value, with the digest left-zero-padded. -/
def generatedPaddedDigest : ByteArray := ByteArray.mk #[
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x97, 0x61, 0x32, 0xce, 0xa9, 0xa6, 0xad, 0x96, 0x0a, 0x57,
  0xa6, 0x5f, 0x7f, 0x0a, 0xfe, 0x0b, 0x0e, 0x3a, 0x01, 0x84]

/-- The word returned by `CALLDATALOAD 0` for the exact 32-byte input. -/
def generatedWord : UInt256 :=
  0x73ddde170c56696f8be0417dea23e4835ef631c760bbc9fbe962885aed87d442

/-- The stored digest word used by the appended return arm. -/
def generatedDigestWord : UInt256 :=
  0x000000000000000000000000976132cea9a6ad960a57a65f7f0afe0b0e3a0184

@[simp] theorem generatedInput_size : generatedInput.size = 32 := by rfl
@[simp] theorem generatedDigest_size : generatedDigest.size = 20 := by rfl
@[simp] theorem generatedPaddedDigest_size : generatedPaddedDigest.size = 32 := by rfl

theorem readWord_generatedInput :
    MachineState.readWord generatedInput 0 = generatedWord := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  change Data.Bytes.bytesToBigEndianNat (MachineState.readPadded generatedInput 0 32) = _
  rw [← Challenge.EvmProof.Bytes.bytesNat_toList,
    Challenge.EvmProof.Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

/-- A full 32-byte calldata word pins the complete input. -/
theorem input_eq_generated (input : ByteArray) (hsize : input.size = 32)
    (hword : MachineState.readWord input 0 = generatedWord) :
    input = generatedInput := by
  apply Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition.byteArray_eq_of_readWord_cover
    input generatedInput
  · exact hsize.trans generatedInput_size.symm
  · intro k hk
    have hk0 : k = 0 := by omega
    subst k
    simpa using hword.trans readWord_generatedInput.symm

end Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedInputData
