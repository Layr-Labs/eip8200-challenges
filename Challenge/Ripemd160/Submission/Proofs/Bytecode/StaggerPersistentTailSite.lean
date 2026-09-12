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
    (Artifact.submissionArtifact.instructions.drop 3774).take template.length = template := by rfl

def site : GenericRoundSite Artifact.submissionArtifact .Osaka template :=
  StackSiteBuilder.ofSlice template 3774 actual_slice
    (by change 3774 + template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := template) (by decide)) (by decide)

theorem site_pc : site.startPC = UInt256.ofNat 4545 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3774) = UInt256.ofNat 4545
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem advances : ∀ instruction ∈ template, DenseScheduleLift.Advances instruction :=
  Table80SiteCommon.coreAdvancesAll_sound template (by decide)

def gasSteps_prefix (s : State) (off limit : UInt256) (h : Compression.HashState)
    (q : StaggerPersistentTailRaw.Input) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4545, stack := StaggerPersistentTailRaw.stack0 (StaggerPersistentFrame.bind h {q with off := off, limit := limit}) rho}
      {s with pc := UInt256.ofNat 4610, stack := StaggerPersistentFrame.frame (StaggerPersistentFrame.combine h q) off limit rho} := by
  apply DenseScheduleLift.gasSteps_of_raw site
    {s with pc := UInt256.ofNat 4545, stack := StaggerPersistentTailRaw.stack0 (StaggerPersistentFrame.bind h {q with off := off, limit := limit}) rho}
    {s with pc := UInt256.ofNat 4610, stack := StaggerPersistentFrame.frame (StaggerPersistentFrame.combine h q) off limit rho}
    hcode hfork hrun hnp site_pc.symm advances
  have hraw := StaggerPersistentFrame.run_tail s (UInt256.ofNat 4545) h {q with off := off, limit := limit} rho hstack hrun
  have hend : pcAfter (UInt256.ofNat 4545) template = UInt256.ofNat 4610 := by decide
  rw [hend] at hraw
  exact hraw

def jumpTemplate : List Instr := PadJump.template 471

theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 3834).take jumpTemplate.length = jumpTemplate := by rfl

def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpTemplate :=
  StackSiteBuilder.ofSlice jumpTemplate 3834 jump_slice
    (by change 3834 + jumpTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := jumpTemplate) (by decide)) (by decide)

theorem jump_pc : jumpSite.startPC = UInt256.ofNat 4610 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3834) = UInt256.ofNat 4610
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem jump_advances : ∀ instruction ∈ jumpTemplate.dropLast, PadLift.Advances instruction :=
  PadLift.advancesAll_sound _ (by decide)

theorem valid_driver (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 471).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 286 = 471 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 286 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 471 = true
  rw [hcode]
  exact h

def gasSteps_jump (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1022)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4610, stack := rho}
      {s with pc := UInt256.ofNat 471, stack := rho} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 4610, stack := rho} _
    hcode hfork hrun hnp jump_pc.symm jump_advances
  exact PadJump.run_template s (UInt256.ofNat 4610) rho 471 hstack hrun (valid_driver s hcode)

def gasSteps (s : State) (off limit : UInt256) (h : Compression.HashState)
    (q : StaggerPersistentTailRaw.Input) (rho : List UInt256) (hstack : rho.length ≤ 980)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4545, stack := StaggerPersistentTailRaw.stack0 (StaggerPersistentFrame.bind h {q with off := off, limit := limit}) rho}
      {s with pc := UInt256.ofNat 471, stack := StaggerPersistentFrame.frame (StaggerPersistentFrame.combine h q) off limit rho} := by
  exact (gasSteps_prefix s off limit h q rho hstack hrun hcode hfork hnp).trans
    (gasSteps_jump s (StaggerPersistentFrame.frame (StaggerPersistentFrame.combine h q) off limit rho)
      (by simp only [StaggerPersistentFrame.frame, List.length_append, List.length_cons, List.length_nil]; omega)
      hrun hcode hfork hnp)
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentTailSite
