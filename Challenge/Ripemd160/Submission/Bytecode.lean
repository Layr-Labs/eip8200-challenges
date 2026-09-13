import Challenge.EvmProof.Bytecode
import Challenge.Ripemd160.Submission.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000

/-!
# Structural binding for the frozen raw-EVM RIPEMD-160 artifact

The candidate bytecode has 5183 bytes and SHA-256 `27b9e0c0480e8a5ba0ca66386ba6b490311c7e3c12afd2b95564b3ac20fd9163`. The hex file remains the external raw input.
-/

namespace Challenge.Ripemd160

open EvmSemantics

def submissionHex : String := (include_str "bytecode.hex").trimAscii.copy

set_option maxRecDepth 50000 in
def submissionBytecode : ByteArray := submissionBytes

set_option maxRecDepth 50000 in
@[simp] theorem referenceBytecode_size : submissionBytecode.size = 5183 := by
  simp [submissionBytecode]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
@[simp] theorem referenceBytecode_get_zero : submissionBytecode[0] = 0x5f := by
  simp only [submissionBytecode]
  exact referenceBytes_get_zero

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
@[simp] theorem referenceBytecode_extract_entry :
    submissionBytecode.extract 1 2 = ByteArray.mk #[0x35] := by
  simp only [submissionBytecode]
  exact referenceBytes_extract_entry

@[simp] theorem bytesToBigEndianNat_entry_literal :
    EvmSemantics.Data.Bytes.bytesToBigEndianNat
      (ByteArray.mk #[0x35]) = 0x35 := by
  simp [EvmSemantics.Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data, UInt8.toNat_ofNat]

@[simp] theorem referenceBytecode_entry_value :
    EvmSemantics.Data.Bytes.bytesToBigEndianNat
      (submissionBytecode.extract 1 2) = 0x35 := by
  rw [referenceBytecode_extract_entry]
  exact bytesToBigEndianNat_entry_literal

theorem referenceBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble submissionBytecode) = submissionBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Ripemd160
