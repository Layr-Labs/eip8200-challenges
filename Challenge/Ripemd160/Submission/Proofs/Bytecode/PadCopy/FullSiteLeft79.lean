import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawLeft79
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Zero
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ModFoldLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullRawLeft79
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullSiteLeft79
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
abbrev template := Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullRawLeft79.template
abbrev inputStack := Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawLeft79.inputStack
abbrev outputStack := Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawLeft79.outputStack
theorem actual_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 6973).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 6973 actual_slice
    (by change 6973 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 10188 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 6973) = UInt256.ofNat 10188
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, HoistedInherited.ModFoldLift.Advances instruction := by
  apply HoistedInherited.ModFoldLift.advancesAll_sound
  decide

def gasSteps (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 901) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) (hz : PadZero s.memory) (hc6 : x.v6 = UInt256.ofNat 0) :
    GasSteps {s with pc := UInt256.ofNat 10188, stack := Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawLeft79.inputStack x rho}
      {s with pc := UInt256.ofNat 10207, stack := Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawLeft79.outputStack s.memory x rho} := by
  have hraw := Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullRawLeft79.run_actual s (UInt256.ofNat 10188) x rho hstack hrun hactive (hz 11 (by decide)) hc6
  have hend : pcAfter (UInt256.ofNat 10188) template = UInt256.ofNat 10207 := by decide
  rw [hend] at hraw
  exact HoistedInherited.ModFoldLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.FullSiteLeft79
