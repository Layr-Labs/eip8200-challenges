import Challenge.EvmProof.Bytecode
import Challenge.Ripemd160.Submission.Bytes
import EvmSemantics.Data.Hex
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# The frozen raw-EVM RIPEMD-160 artifact

`submissionBytecode` is the exact combined H30b+H31b bytecode from the frozen native
checkpoint. It preserves the H30b prefix while replacing the left R1 wrapper
transfer with a width-preserving entry jump and appending the inline R1 body.
The existing B01 transform is not reapplied.

Correctness proofs target these bytes directly; the compiler is used to
reproduce the artifact, not as an assumption in the bytecode proof.
-/

namespace Challenge.Ripemd160

open EvmSemantics

def submissionHex : String := (include_str "bytecode.hex").trimAscii.copy

set_option maxRecDepth 50000 in
def submissionBytecode : ByteArray := submissionBytes

set_option maxRecDepth 50000 in
@[simp] theorem referenceBytecode_size : submissionBytecode.size = 5953 := by
  simp [submissionBytecode]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
@[simp] theorem referenceBytecode_get_zero : submissionBytecode[0] = 0x5b := by
  simp only [submissionBytecode]
  exact referenceBytes_get_zero

theorem referenceBytecode_roundtrip :
    Challenge.EvmProof.Bytecode.assemble
      (Challenge.EvmProof.Bytecode.disassemble submissionBytecode) = submissionBytecode :=
  Challenge.EvmProof.Bytecode.assemble_disassemble _

end Challenge.Ripemd160
