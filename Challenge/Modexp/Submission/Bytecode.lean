import Challenge.EvmProof.Bytecode
import Challenge.Modexp.Submission.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp

def submissionHex : String := (include_str "bytecode.hex").trimAscii.copy
def submissionBytecode : ByteArray := submissionBytes

@[simp] theorem submissionBytecode_size : submissionBytecode.size = 5428 := by
  change submissionBytes.size = 5428
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

-- packaging revision 20260916T015640Z

-- packaging revision 20260916T023914Z

-- packaging revision 20260916T032612Z

-- packaging revision 20260916T041924Z

-- packaging revision 20260916T050416Z

-- packaging revision 20260916T055714Z

-- packaging revision 20260916T065328Z

-- packaging revision 20260916T073903Z

-- packaging revision 20260916T204559Z

-- packaging revision 20260916T222835Z

-- packaging revision 20260916T231346Z

-- packaging revision 20260916T231555Z

-- packaging revision 20260916T231802Z
