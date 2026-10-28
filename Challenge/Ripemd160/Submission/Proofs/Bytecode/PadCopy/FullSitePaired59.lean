import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawPaired59
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Zero
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ModFoldLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullRawPaired59
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullSitePaired59
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
abbrev template := Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullRawPaired59.template
abbrev inputStack := Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawPaired59.inputStack
abbrev outputStack := Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawPaired59.outputStack
theorem actual_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 5446).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 5446 actual_slice
    (by change 5446 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 7324 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 5446) = UInt256.ofNat 7324
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
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) (hc4 : x.v4 = UInt256.ofNat 0) :
    GasSteps {s with pc := UInt256.ofNat 7324, stack := Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawPaired59.inputStack x rho}
      {s with pc := UInt256.ofNat 7372, stack := Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired59.outputStack s.memory x rho} := by
  have hraw := Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullRawPaired59.run_actual s (UInt256.ofNat 7324) x rho hstack hrun hactive (hz 36 (by decide)) hc4
  have hend : pcAfter (UInt256.ofNat 7324) template = UInt256.ofNat 7372 := by decide
  rw [hend] at hraw
  exact HoistedInherited.ModFoldLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullSitePaired59
