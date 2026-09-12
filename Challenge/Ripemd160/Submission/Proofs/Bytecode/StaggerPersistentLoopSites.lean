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

def postTemplate : List Instr := StaggerPersistentLoopRaw.template 465

theorem post_slice :
    (Artifact.submissionArtifact.instructions.drop 3785).take postTemplate.length = postTemplate := by rfl

def postSite : GenericRoundSite Artifact.submissionArtifact .Osaka postTemplate :=
  StackSiteBuilder.ofSlice postTemplate 3785 post_slice
    (by change 3785 + postTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := postTemplate) (by decide))
    (by decide)

theorem post_pc : postSite.startPC = UInt256.ofNat 4723 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3785) = UInt256.ofNat 4723
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def joinTemplate : List Instr := [.op .JUMPDEST]

theorem join_slice :
    (Artifact.submissionArtifact.instructions.drop 281).take joinTemplate.length = joinTemplate := by rfl

def joinSite : GenericRoundSite Artifact.submissionArtifact .Osaka joinTemplate :=
  StackSiteBuilder.ofSlice joinTemplate 281 join_slice
    (by change 281 + joinTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := joinTemplate) (by decide))
    (by decide)

theorem join_pc : joinSite.startPC = UInt256.ofNat 465 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 281) = UInt256.ofNat 465
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 465).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 281 = 465 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 281 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 465 = true
  rw [hcode]
  exact h

def gasSteps_join (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 465, stack := rho}
      {s with pc := UInt256.ofNat 466, stack := rho} := by
  apply PadLift.gasSteps_of_raw joinSite {s with pc := UInt256.ofNat 465, stack := rho} _
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
    GasSteps {s with pc := UInt256.ofNat 4723, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 466, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  have gp : GasSteps {s with pc := UInt256.ofNat 4723, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 465, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
    apply PersistentLoopLift.gasSteps_of_raw postSite {s with pc := UInt256.ofNat 4723, stack := StaggerPersistentFrame.frame h off limit rho} _ hcode hfork hrun hnp post_pc.symm
    · exact PersistentLoopLift.advancesAll_sound _ (by decide)
    · exact run_continue s (UInt256.ofNat 4723) h off limit rho 465 hstack hrun hmiss (valid_loop s hcode)
  exact gp.trans (gasSteps_join s (StaggerPersistentFrame.frame h (nextOffset off) limit rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp)

def gasSteps_exit (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 1013) (hrun : s.halt = .Running)
    (hhit : (nextOffset off).toNat = limit.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4723, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4736, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  apply PersistentLoopLift.gasSteps_of_raw postSite {s with pc := UInt256.ofNat 4723, stack := StaggerPersistentFrame.frame h off limit rho} _ hcode hfork hrun hnp post_pc.symm
  · exact PersistentLoopLift.advancesAll_sound _ (by decide)
  · have hr := run_exit s (UInt256.ofNat 4723) h off limit rho 465 hstack hrun hhit
    have he : pcAfter (UInt256.ofNat 4723) (StaggerPersistentLoopRaw.template 465) = UInt256.ofNat 4736 := by decide
    rw [he] at hr
    exact hr
#print axioms gasSteps_continue
#print axioms gasSteps_exit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
