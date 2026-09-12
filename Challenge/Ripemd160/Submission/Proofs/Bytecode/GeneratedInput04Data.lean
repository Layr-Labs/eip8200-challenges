import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedInput04Data

open EvmSemantics EvmSemantics.EVM

/-- Seeded corpus vector `generated #04` from the pinned scorer. -/
def generatedInput : ByteArray := ByteArray.mk #[
  0x94, 0xcf, 0x1a, 0xe9, 0x79, 0x77, 0x7b, 0xb0,
  0xe2, 0x63, 0x75, 0x25, 0xe8, 0xcc, 0xa0, 0x4e,
  0x99, 0x57, 0xbd, 0x78, 0x6a, 0x07, 0x7e, 0xfc,
  0x26, 0x3f, 0x33, 0x36, 0xe7, 0x4a, 0xd0, 0x5d]

/-- `RIPEMD160 generatedInput`, in the scorer's 20-byte return format. -/
def generatedDigest : ByteArray := ByteArray.mk #[
  0x39, 0xdb, 0xb2, 0xe2, 0xb8, 0x9c, 0xa9, 0x2e, 0x91, 0x03,
  0x4d, 0xaa, 0xc3, 0xde, 0x29, 0x63, 0x93, 0xd7, 0xb8, 0xf6]

/-- The 32-byte return value, with the digest left-zero-padded. -/
def generatedPaddedDigest : ByteArray := ByteArray.mk #[
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x39, 0xdb, 0xb2, 0xe2, 0xb8, 0x9c, 0xa9, 0x2e, 0x91, 0x03,
  0x4d, 0xaa, 0xc3, 0xde, 0x29, 0x63, 0x93, 0xd7, 0xb8, 0xf6]

/-- The word returned by `CALLDATALOAD 0` for the exact 32-byte input. -/
def generatedWord : UInt256 :=
  0x94cf1ae979777bb0e2637525e8cca04e9957bd786a077efc263f3336e74ad05d

/-- The stored digest word used by the appended return arm. -/
def generatedDigestWord : UInt256 :=
  0x00000000000000000000000039dbb2e2b89ca92e91034daac3de296393d7b8f6

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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedInput04Data
