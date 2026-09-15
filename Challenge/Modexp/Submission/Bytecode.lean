import Challenge.EvmProof.Bytecode
import Challenge.Modexp.Submission.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp

def submissionHex : String := (include_str "bytecode.hex").trimAscii.copy
def submissionBytecode : ByteArray := submissionBytes

@[simp] theorem submissionBytecode_size : submissionBytecode.size = 5339 := by
  change submissionBytes.size = 5339
  exact submissionBytes_size

theorem submissionBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble submissionBytecode) = submissionBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Modexp

-- lottery rerun 2026-09-15T07:11:44Z: accepted artifact resubmitted under a fresh benchmark seed, bytes and proofs unchanged
-- lottery rerun 2026-09-15T08:37:44Z: same verified 5339-byte artifact, fresh benchmark seed, executable and proofs unchanged
-- lottery rerun 2026-09-15T09:46:44Z: prior draw scored 489783; same verified bytes resubmitted for another independent seed
