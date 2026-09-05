import Challenge.EvmProof.Bytecode
import Challenge.Ripemd160.Submission.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# The frozen raw-EVM RIPEMD-160 artifact

`submissionBytecode` is the exact H23 bytecode from the frozen native checkpoint. It
retains the original 1830-byte prefix; the existing B01 transform is not reapplied.

Correctness proofs target these bytes directly; the compiler is used to
reproduce the artifact, not as an assumption in the bytecode proof.
-/

namespace Challenge.Ripemd160

open EvmSemantics

def submissionHex : String := (include_str "bytecode.hex").trimAscii.copy

set_option maxRecDepth 50000 in
def submissionBytecode : ByteArray := submissionBytes

set_option maxRecDepth 50000 in
@[simp] theorem referenceBytecode_size : submissionBytecode.size = 5299 := by
  simp [submissionBytecode]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
@[simp] theorem referenceBytecode_get_zero : submissionBytecode[0] = 0x61 := by
  simp only [submissionBytecode]
  exact referenceBytes_get_zero

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
@[simp] theorem referenceBytecode_extract_entry :
    submissionBytecode.extract 1 3 = ByteArray.mk #[0x14, 0x92] := by
  simp only [submissionBytecode]
  exact referenceBytes_extract_entry

@[simp] theorem bytesToBigEndianNat_entry_literal :
    EvmSemantics.Data.Bytes.bytesToBigEndianNat
      (ByteArray.mk #[0x14, 0x92]) = 0x1492 := by
  simp [EvmSemantics.Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data, UInt8.toNat_ofNat]

@[simp] theorem referenceBytecode_entry_value :
    EvmSemantics.Data.Bytes.bytesToBigEndianNat
      (submissionBytecode.extract 1 3) = 0x1492 := by
  rw [referenceBytecode_extract_entry]
  exact bytesToBigEndianNat_entry_literal

theorem referenceBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble submissionBytecode) = submissionBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Ripemd160
