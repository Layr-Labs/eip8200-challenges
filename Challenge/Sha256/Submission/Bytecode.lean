import Challenge.EvmProof.Bytecode
import Challenge.Sha256.Submission.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# The frozen raw-EVM SHA-256 artifact

`submissionBytecode` is the byte-for-byte output of:

```sh
lake exe yulc Challenge/Sha256/Reference/reference.yul
```

The compiler is used only to generate the artifact. direct-bytecode proofs target
these frozen bytes and reason through `EvmSemantics.EVM.Step`; they do not
appeal to compiler correctness.
-/

namespace Challenge.Sha256

open EvmSemantics
/-- The canonical hexadecimal form of the submitted artifact. -/
def submissionHex : String :=
  (include_str "bytecode.hex").trimAscii.copy

/-- The submitted SHA-256 bytecode. Its literal form is definitionally
reducible for direct `stepF` proofs; CI pins it to `reference.hex`. -/
def submissionBytecode : ByteArray := submissionBytes

@[simp] theorem submissionBytecode_size : submissionBytecode.size = 1524 := by
  simp [submissionBytecode]

@[simp] theorem submissionBytecode_get_zero : submissionBytecode[0] = 0x61 := by
  change submissionBytes[0] = 0x61
  exact submissionBytes_get_zero

@[simp] theorem submissionBytecode_extract_entry :
    submissionBytecode.extract 1 3 = ByteArray.mk #[0x03, 0xe5] := by
  change submissionBytes.extract 1 3 = ByteArray.mk #[0x03, 0xe5]
  exact submissionBytes_extract_entry

@[simp] theorem bytesToBigEndianNat_entry_literal :
    EvmSemantics.Data.Bytes.bytesToBigEndianNat
      (ByteArray.mk #[0x03, 0xe5]) = 0x03e5 := by
  simp [EvmSemantics.Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data, UInt8.toNat_ofNat]

@[simp] theorem submissionBytecode_entry_value :
    EvmSemantics.Data.Bytes.bytesToBigEndianNat
      (submissionBytecode.extract 1 3) = 0x03e5 := by
  rw [submissionBytecode_extract_entry]
  exact bytesToBigEndianNat_entry_literal

/-- The generic direct-bytecode disassembler round-trips the frozen artifact. -/
theorem submissionBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble submissionBytecode) = submissionBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Sha256
