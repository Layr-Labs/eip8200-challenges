import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired72Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Table80SiteCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawPaired72
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired72
abbrev template := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired72.template
abbrev inputStack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired72.inputStack
abbrev outputStack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired72.outputStack
theorem actual_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 3068).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3068 actual_slice
    (by change 3068 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 4246 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 3068) = UInt256.ofNat 4246
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply HoistedInherited.Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4246, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 4282, stack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired72.outputStack s.memory x rho} := by
  have hraw := run_actual s (UInt256.ofNat 4246) x rho hstack hrun hactive
  have hend : pcAfter (UInt256.ofNat 4246) template = UInt256.ofNat 4282 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawPaired72
