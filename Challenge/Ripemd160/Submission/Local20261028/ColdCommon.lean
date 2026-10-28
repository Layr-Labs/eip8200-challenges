import Challenge.Ripemd160.Submission.Local20261028.ColdArtifact
import Challenge.Ripemd160.Submission.Local20261028.CoreGas
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.StackRoundData
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
theorem artifact_code_bound : CandidateArtifact.artifact.code.size < 2^256 := by
  rw [CandidateArtifact.code_size]; decide
 theorem templateWellFormed_mem {instructions : List Instr}
    (h : instructions.all CoreGas.wellFormedCheck = true) :
    ∀ i ∈ instructions, DataStepper.WellFormed .Osaka i := CoreGas.wellFormed_of_check instructions h
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.StackRoundData
