import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentLoopLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentLoopRaw

def postTemplate : List Instr := StaggerPersistentLoopRaw.template 471

theorem post_slice :
    (Artifact.submissionArtifact.instructions.drop 3796).take postTemplate.length = postTemplate := by rfl

def postSite : GenericRoundSite Artifact.submissionArtifact .Osaka postTemplate :=
  StackSiteBuilder.ofSlice postTemplate 3796 post_slice
    (by change 3796 + postTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := postTemplate) (by decide))
    (by decide)

theorem post_pc : postSite.startPC = UInt256.ofNat 4735 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3796) = UInt256.ofNat 4735
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def joinTemplate : List Instr := [.op .JUMPDEST]

theorem join_slice :
    (Artifact.submissionArtifact.instructions.drop 286).take joinTemplate.length = joinTemplate := by rfl

def joinSite : GenericRoundSite Artifact.submissionArtifact .Osaka joinTemplate :=
  StackSiteBuilder.ofSlice joinTemplate 286 join_slice
    (by change 286 + joinTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := joinTemplate) (by decide))
    (by decide)

theorem join_pc : joinSite.startPC = UInt256.ofNat 471 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 286) = UInt256.ofNat 471
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 471).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 286 = 471 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 286 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 471 = true
  rw [hcode]
  exact h

def gasSteps_join (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 471, stack := rho}
      {s with pc := UInt256.ofNat 472, stack := rho} := by
  apply PadLift.gasSteps_of_raw joinSite {s with pc := UInt256.ofNat 471, stack := rho} _
    hcode hfork hrun hnp join_pc.symm
  · apply PadLift.advancesAll_sound
    decide
  · simp [joinTemplate, runInstrSeq, Stepper.runInstr, hrun, hstack]
    rfl

def gasSteps_continue (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hmiss : (nextOffset off).toNat ≠ limit.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4735, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 472, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  have gp : GasSteps {s with pc := UInt256.ofNat 4735, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 471, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
    apply PersistentLoopLift.gasSteps_of_raw postSite {s with pc := UInt256.ofNat 4735, stack := StaggerPersistentFrame.frame h off limit rho} _ hcode hfork hrun hnp post_pc.symm
    · exact PersistentLoopLift.advancesAll_sound _ (by decide)
    · exact run_continue s (UInt256.ofNat 4735) h off limit rho 471 hstack hrun hmiss (valid_loop s hcode)
  exact gp.trans (gasSteps_join s (StaggerPersistentFrame.frame h (nextOffset off) limit rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp)

def gasSteps_exit (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hhit : (nextOffset off).toNat = limit.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4735, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4748, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  apply PersistentLoopLift.gasSteps_of_raw postSite {s with pc := UInt256.ofNat 4735, stack := StaggerPersistentFrame.frame h off limit rho} _ hcode hfork hrun hnp post_pc.symm
  · exact PersistentLoopLift.advancesAll_sound _ (by decide)
  · have hr := run_exit s (UInt256.ofNat 4735) h off limit rho 471 hstack hrun hhit
    have he : pcAfter (UInt256.ofNat 4735) (StaggerPersistentLoopRaw.template 471) = UInt256.ofNat 4748 := by decide
    rw [he] at hr
    exact hr
#print axioms gasSteps_continue
#print axioms gasSteps_exit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
