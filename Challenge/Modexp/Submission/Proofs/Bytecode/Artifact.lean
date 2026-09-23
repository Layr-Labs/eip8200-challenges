import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Bytecode
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
abbrev submissionInstructions := TnM128CandidateArtifact.submissionInstructions
abbrev submissionInstructions_count := TnM128CandidateArtifact.submissionInstructions_count
theorem assemble_submissionInstructions : assemble submissionInstructions =
    Challenge.Modexp.submissionBytecode := by
  exact TnM128CandidateArtifact.assemble_submissionInstructions

def submissionArtifact : Challenge.EvmProof.ProgramArtifact where
  code := Challenge.Modexp.submissionBytecode
  instructions := submissionInstructions
  assembly_eq := assemble_submissionInstructions

theorem allWellFormed : Challenge.EvmProof.Stepper.AllWellFormed submissionArtifact .Osaka := by
  exact TnM128CandidateArtifact.allWellFormed
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
def instructionPC (index : Nat) : Nat := submissionArtifact.instructionPC index

theorem decodeAt_op_index (index : Nat) (op : Operation)
    (hget : submissionInstructions[index]? = some (.op op))
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op) :
    Decode.decodeAt Challenge.Modexp.submissionBytecode (instructionPC index) = some (op, none) :=
  Challenge.EvmProof.ProgramArtifact.decodeAt_op_index
    submissionArtifact index op hget hopcode hplain

theorem decodeAt_push_index (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : submissionInstructions[index]? = some (.push width value))
    (hfit : value.toNat < 256 ^ width.val) :
    Decode.decodeAt Challenge.Modexp.submissionBytecode (instructionPC index) =
      some (.Push ⟨width⟩, some (value, width.val)) :=
  Challenge.EvmProof.ProgramArtifact.decodeAt_push_index
    submissionArtifact index width value hget hfit

theorem isValidJumpDest_index (index : Nat)
    (hget : submissionInstructions[index]? = some (.op .JUMPDEST)) :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (instructionPC index) = true :=
  Challenge.EvmProof.ProgramArtifact.isValidJumpDest_index
    submissionArtifact index hget

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
