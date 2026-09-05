import Challenge.EvmProof.Bytecode
import Challenge.Ripemd160.Submission.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# The frozen raw-EVM RIPEMD-160 artifact

`submissionBytecode` is the byte-for-byte output of:

```sh
lake exe yulc Challenge/Ripemd160/Reference/reference.yul
```

Correctness proofs target these bytes directly; the compiler is used to
reproduce the artifact, not as an assumption in the bytecode proof.
-/

namespace Challenge.Ripemd160

open EvmSemantics

def submissionHex : String := (include_str "bytecode.hex").trimAscii.copy

def submissionBytecode : ByteArray := submissionBytes

@[simp] theorem referenceBytecode_size : submissionBytecode.size = 1830 := by
  simp [submissionBytecode]

@[simp] theorem referenceBytecode_get_zero : submissionBytecode[0] = 0x61 := by
  change submissionBytes[0] = 0x61
  exact referenceBytes_get_zero

@[simp] theorem referenceBytecode_extract_entry :
    submissionBytecode.extract 1 3 = ByteArray.mk #[0x03, 0xee] := by
  change submissionBytes.extract 1 3 = ByteArray.mk #[0x03, 0xee]
  exact referenceBytes_extract_entry

@[simp] theorem bytesToBigEndianNat_entry_literal :
    EvmSemantics.Data.Bytes.bytesToBigEndianNat
      (ByteArray.mk #[0x03, 0xee]) = 0x03ee := by
  simp [EvmSemantics.Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data, UInt8.toNat_ofNat]

@[simp] theorem referenceBytecode_entry_value :
    EvmSemantics.Data.Bytes.bytesToBigEndianNat
      (submissionBytecode.extract 1 3) = 0x03ee := by
  rw [referenceBytecode_extract_entry]
  exact bytesToBigEndianNat_entry_literal

theorem referenceBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble submissionBytecode) = submissionBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Ripemd160
