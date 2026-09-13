import Challenge.EvmProof.Bytecode
import Challenge.Modexp.Submission.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp

def submissionHex : String := (include_str "bytecode.hex").trimAscii.copy
def submissionBytecode : ByteArray := submissionBytes

@[simp] theorem submissionBytecode_size : submissionBytecode.size = 5300 := by
  change submissionBytes.size = 5300
  exact submissionBytes_size

theorem submissionBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble submissionBytecode) = submissionBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Modexp

-- lottery rerun 2026-09-13T16:29:36Z: public PR #1613 artifact resubmitted under a fresh benchmark seed, bytes and proofs unchanged

-- lottery rerun 2026-09-13T19:37:35Z: public PR #1635 artifact resubmitted under a fresh benchmark seed, bytes and proofs unchanged
