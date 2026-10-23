import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired2Raw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Table80SiteCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawPaired2
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired2
abbrev template := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired2.template
abbrev inputStack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired2.inputStack
abbrev outputStack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired2.outputStack
theorem actual_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 557).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 557 actual_slice
    (by change 557 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 1111 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 557) = UInt256.ofNat 1111
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
    GasSteps {s with pc := UInt256.ofNat 1111, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 1149, stack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired2.outputStack s.memory x rho} := by
  have hraw := run_actual s (UInt256.ofNat 1111) x rho hstack hrun hactive
  have hend : pcAfter (UInt256.ofNat 1111) template = UInt256.ofNat 1149 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawPaired2
