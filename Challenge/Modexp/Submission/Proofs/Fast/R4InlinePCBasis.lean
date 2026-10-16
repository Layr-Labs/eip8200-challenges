import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Mathlib.Data.List.TakeDrop
set_option warningAsError true
namespace Challenge.Modexp.Submission.Proofs.Fast.R4InlinePCBasis
open YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode

theorem byteLength_append (left right : List Instr) :
    PCFast.byteLength (left ++ right) = PCFast.byteLength left + PCFast.byteLength right := by
  simp only [PCFast.byteLength_eq_assemble, assembleBytes_append, List.length_append]

theorem instructionPC_add (artifact : ProgramArtifact) (start offset : Nat) :
    artifact.instructionPC (start + offset) =
      artifact.instructionPC start + PCFast.byteLength ((artifact.instructions.drop start).take offset) := by
  simp only [PCFast.instructionPC_eq_byteLength, List.take_add, byteLength_append]

end Challenge.Modexp.Submission.Proofs.Fast.R4InlinePCBasis
