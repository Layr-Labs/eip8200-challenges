import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.Zero
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option maxRecDepth 200000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SiteBootstrap
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentBootstrapRaw
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy (PadZero)
theorem actual_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 3856).take template.length = template := by rfl

def site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3856 actual_slice
    (by change 3856 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 6154 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 3856) = UInt256.ofNat 6154
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  apply HoistedInherited.Table80SiteCommon.coreAdvancesAll_sound
  decide

def gasSteps (s : State) (x : Input) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hz : PadZero s.memory) :
    GasSteps {s with pc := UInt256.ofNat 6154, stack := inputStack x rho}
      {s with pc := UInt256.ofNat 6155, stack := outputStack s.memory x rho} := by
  have hraw := run_actual s (UInt256.ofNat 6154) x rho hs hr ha
  have hend : pcAfter (UInt256.ofNat 6154) template = UInt256.ofNat 6155 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw site _ _ hcode hfork hr hnp site_pc.symm advances hraw

#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.SiteBootstrap
