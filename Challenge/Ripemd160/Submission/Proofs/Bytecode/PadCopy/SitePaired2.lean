import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawPaired2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawPaired2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Zero
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SitePaired2
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
abbrev template := Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawPaired2.template
abbrev inputStack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired2.inputStack
abbrev outputStack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired2.outputStack
theorem actual_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 4032).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 4032 actual_slice
    (by change 4032 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 6424 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 4032) = UInt256.ofNat 6424
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
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hz : PadZero s.memory) (hc0 : x.v2 = UInt256.ofNat 0) :
    GasSteps {s with pc := UInt256.ofNat 6424, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 6460, stack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired2.outputStack s.memory x rho} := by
  have hraw := Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawPaired2.run_actual s (UInt256.ofNat 6424) x rho hstack hrun hactive hc0
  have hend : pcAfter (UInt256.ofNat 6424) template = UInt256.ofNat 6460 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SitePaired2
