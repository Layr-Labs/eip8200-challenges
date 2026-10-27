import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawPaired11
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawPaired11
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Zero
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SitePaired11
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
abbrev template := Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawPaired11.template
abbrev inputStack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired11.inputStack
abbrev outputStack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired11.outputStack
theorem actual_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 4482).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 4482 actual_slice
    (by change 4482 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 7296 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 4482) = UInt256.ofNat 7296
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, HoistedInherited.ModFoldLift.Advances instruction := by
  apply HoistedInherited.ModFoldLift.advancesAll_sound
  decide

def gasSteps (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hz : PadZero s.memory) :
    GasSteps {s with pc := UInt256.ofNat 7296, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 7341, stack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired11.outputStack s.memory x rho} := by
  have hraw := Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawPaired11.run_actual s (UInt256.ofNat 7296) x rho hstack hrun hactive (hz 48 (by decide))
  have hend : pcAfter (UInt256.ofNat 7296) template = UInt256.ofNat 7341 := by decide
  rw [hend] at hraw
  exact HoistedInherited.ModFoldLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SitePaired11
