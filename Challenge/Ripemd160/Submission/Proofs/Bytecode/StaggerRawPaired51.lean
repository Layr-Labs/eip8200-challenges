import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired51Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ModFoldLift
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired51
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 2556).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 2556 actual_slice
    (by change 2556 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 3278 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2556) = UInt256.ofNat 3278
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
    GasSteps {s with pc := UInt256.ofNat 3278, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 3334, stack := outputStack s.memory x rho} := by
  have hraw := run_actual s (UInt256.ofNat 3278) x rho hstack hrun hactive
  have hend : pcAfter (UInt256.ofNat 3278) template = UInt256.ofNat 3334 := by decide
  rw [hend] at hraw
  exact ModFoldLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired51
