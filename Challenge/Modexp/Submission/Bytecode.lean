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

-- packaging revision 20260915T231210Z

-- packaging revision 20260915T234013Z

-- packaging revision 20260916T002555Z

-- packaging revision 20260916T010908Z

-- lottery rerun 2026-09-16T13:48:00Z: accepted artifact resubmitted under a fresh benchmark seed, bytes and proofs unchanged

-- lottery rerun 2026-09-16T14:46:11Z: accepted artifact resubmitted under a fresh benchmark seed, bytes and proofs unchanged
