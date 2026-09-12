import Challenge.EvmProof.Program
import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word
import Challenge.Modexp.Submission.Bytecode

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactChunks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler

@[simp] theorem assemble_append (xs ys : List Instr) :
    assemble (xs ++ ys) = assemble xs ++ assemble ys := by
  apply ByteArray.ext
  simp [assemble, assembleBytes_append, ByteArray.data_append]

end Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactChunks
