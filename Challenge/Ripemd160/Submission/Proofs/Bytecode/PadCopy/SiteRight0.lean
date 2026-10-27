import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawRight0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawRight0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Zero
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SiteRight0
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
abbrev template := Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawRight0.template
open Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerRawRight0 (inputStack outputStack)
theorem actual_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 3857).take template.length = template := by rfl
def site : StackRoundTemplate.GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3857 actual_slice
    (by change 3857 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide))
    (by decide)
theorem site_pc : site.startPC = UInt256.ofNat 6155 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 3857) = UInt256.ofNat 6155
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply HoistedInherited.Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps (s : State) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (halias : rho[2]? = some x.v2) (haliasC : rho[1]? = some x.v3) (haliasD : rho[0]? = some x.v4) (haliasA : rho[3]? = some x.v1) (hkey : x.v0 = UInt256.ofNat 1352829926) (haliasE : x.v12 = x.v5) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hz : PadZero s.memory) :
    GasSteps {s with pc := UInt256.ofNat 6155, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 6187, stack := outputStack s.memory x rho} := by
  have hraw := Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawRight0.run_actual s (UInt256.ofNat 6155) x rho hstack halias haliasC haliasD haliasA hkey haliasE hrun hactive (hz 27 (by decide))
  have hend : pcAfter (UInt256.ofNat 6155) template = UInt256.ofNat 6187 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hrun hnp site_pc.symm advances hraw
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SiteRight0
