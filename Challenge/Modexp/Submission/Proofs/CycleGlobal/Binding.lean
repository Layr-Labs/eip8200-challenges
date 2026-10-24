import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Global.Binding
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding

theorem jumpDest (index : Nat)
    (h : Artifact.instructions[index]? = some (.op .JUMPDEST)) :
    Decode.isValidJumpDest Artifact.bytecode (Artifact.artifact.instructionPC index) = true :=
  ProgramArtifact.isValidJumpDest_index Artifact.artifact index h

-- The signature matches the existing slice builder so inherited block records
-- retain their literal program-counter and instruction-count obligations.
abbrev block := @WindowTwentyOneSlice.block

end CycleSubmission.Global.Binding
