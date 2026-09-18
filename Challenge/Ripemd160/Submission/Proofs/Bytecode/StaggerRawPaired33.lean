import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired33Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ModFoldLift
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired33
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 1826).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 1826 actual_slice
    (by change 1826 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 2600 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 1826) = UInt256.ofNat 2600
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, ModFoldLift.Advances instruction := by
  apply ModFoldLift.advancesAll_sound
  decide

def gasSteps (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 2600, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 2648, stack := outputStack s.memory x rho} := by
  have hraw := run_actual s (UInt256.ofNat 2600) x rho hstack hrun hactive
  have hend : pcAfter (UInt256.ofNat 2600) template = UInt256.ofNat 2648 := by decide
  rw [hend] at hraw
  exact ModFoldLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired33
