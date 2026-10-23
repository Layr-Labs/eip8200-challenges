import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ScheduledTailBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerPersistentTailSite
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate
abbrev template := ScheduledTailRaw.template
theorem actual_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 3316).take template.length = template := by rfl

def site : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3316 actual_slice
    (by change 3316 + template.length ≤ HoistedInherited.Artifact.submissionInstructions.length
        rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 4508 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 3316) = UInt256.ofNat 4508
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction :=
  HoistedInherited.Table80SiteCommon.coreAdvancesAll_sound template (by decide)

def gasSteps_prefix (s : State) (off limit : UInt256) (h : Compression.HashState)
    (q : StaggerPersistentTailRaw.Input) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4508, stack := StaggerPersistentTailRaw.entryStack (StaggerPersistentFrame.bind h {q with off := off, limit := limit}) rho}
      {s with pc := UInt256.ofNat 4563, stack := Word.ofUInt32 h.h2 :: StaggerPersistentFrame.frame (StaggerPersistentFrame.combine h q) off limit rho} := by
  apply DenseScheduleLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 4508, stack := StaggerPersistentTailRaw.entryStack (StaggerPersistentFrame.bind h {q with off := off, limit := limit}) rho}
    {s with pc := UInt256.ofNat 4563, stack := Word.ofUInt32 h.h2 :: StaggerPersistentFrame.frame (StaggerPersistentFrame.combine h q) off limit rho}
    hcode hfork hrun hnp site_pc.symm advances
  have hraw := HoistedInherited.ScheduledTailBridge.run_current s (UInt256.ofNat 4508) h {q with off := off, limit := limit} rho hstack hrun
  have hend : pcAfter (UInt256.ofNat 4508) template = UInt256.ofNat 4563 := by decide
  rw [hend] at hraw
  exact hraw

abbrev gasSteps := gasSteps_prefix
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StaggerPersistentTailSite
