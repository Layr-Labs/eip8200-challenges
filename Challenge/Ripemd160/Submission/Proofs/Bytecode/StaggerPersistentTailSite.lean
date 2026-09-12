import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentTailSite
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate
abbrev template := StaggerPersistentTailRaw.template
theorem actual_slice :
    (Artifact.submissionArtifact.instructions.drop 3736).take template.length = template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3736 actual_slice
    (by change 3736 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 4672 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3736) = UInt256.ofNat 4672
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction :=
  Table80SiteCommon.coreAdvancesAll_sound template (by decide)

def gasSteps_prefix (s : State) (off limit : UInt256) (h : Compression.HashState)
    (q : StaggerPersistentTailRaw.Input) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4672, stack := StaggerPersistentTailRaw.stack0 (StaggerPersistentFrame.bind h {q with off := off, limit := limit}) rho}
      {s with pc := UInt256.ofNat 4737, stack := StaggerPersistentFrame.frame (StaggerPersistentFrame.combine h q) off limit rho} := by
  apply DenseScheduleLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 4672, stack := StaggerPersistentTailRaw.stack0 (StaggerPersistentFrame.bind h {q with off := off, limit := limit}) rho}
    {s with pc := UInt256.ofNat 4737, stack := StaggerPersistentFrame.frame (StaggerPersistentFrame.combine h q) off limit rho}
    hcode hfork hrun hnp site_pc.symm advances
  have hraw := StaggerPersistentFrame.run_tail s (UInt256.ofNat 4672) h {q with off := off, limit := limit} rho hstack hrun
  have hend : pcAfter (UInt256.ofNat 4672) template = UInt256.ofNat 4737 := by decide
  rw [hend] at hraw
  exact hraw

abbrev gasSteps := gasSteps_prefix
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentTailSite
