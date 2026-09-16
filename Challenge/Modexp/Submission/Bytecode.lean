import Challenge.EvmProof.Bytecode
import Challenge.Modexp.Submission.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp

def submissionHex : String := (include_str "bytecode.hex").trimAscii.copy
def submissionBytecode : ByteArray := submissionBytes

@[simp] theorem submissionBytecode_size : submissionBytecode.size = 5314 := by
  change submissionBytes.size = 5314
  exact submissionBytes_size

theorem submissionBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble submissionBytecode) = submissionBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Modexp

-- packaging revision 20260916T140625Z

-- packaging revision 20260916T140834Z

-- packaging revision 20260916T141041Z

-- packaging revision 20260916T141248Z

-- packaging revision 20260916T141454Z

-- packaging revision 20260916T141639Z

-- packaging revision 20260916T150550Z
