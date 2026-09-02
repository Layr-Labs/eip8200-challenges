import Challenge.EvmProof.Bytecode
import Challenge.Modexp.Reference.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp

/-- Canonical hexadecimal form of the frozen artifact. -/
def referenceHex : String := (include_str "reference.hex").trimAscii.copy

/-- Frozen verified-compiler output targeted by the direct EVM proof. -/
def referenceBytecode : ByteArray := referenceBytes

@[simp] theorem referenceBytecode_size : referenceBytecode.size = 1284 := by
  change referenceBytes.size = 1284
  exact referenceBytes_size

/-- Generic disassembly round-trip for the exact submitted bytes. -/
theorem referenceBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble referenceBytecode) = referenceBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Modexp
