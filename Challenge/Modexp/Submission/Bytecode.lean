import Challenge.EvmProof.Bytecode
import Challenge.Modexp.Submission.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp

def submissionHex : String := (include_str "bytecode.hex").trimAscii.copy
def submissionBytecode : ByteArray := submissionBytes

@[simp] theorem submissionBytecode_size : submissionBytecode.size = 5310 := by
  change submissionBytes.size = 5310
  exact submissionBytes_size

theorem submissionBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble submissionBytecode) = submissionBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Modexp

-- lottery rerun 2026-09-13T23:44:50Z: public PR #1663 artifact resubmitted under a fresh benchmark seed, bytes and proofs unchanged

-- lottery rerun 2026-09-14T00:51:32Z: accepted artifact resubmitted under a fresh benchmark seed, bytes and proofs unchanged
