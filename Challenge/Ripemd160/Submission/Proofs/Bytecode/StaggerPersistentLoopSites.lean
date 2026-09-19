import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
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

def postTemplate : List Instr := StaggerPersistentLoopRaw.template 486

theorem post_slice :
    (Artifact.submissionArtifact.instructions.drop 3519).take postTemplate.length = postTemplate := by rfl

def postSite : GenericRoundSite Artifact.submissionArtifact .Osaka postTemplate :=
  StackSiteBuilder.ofSlice postTemplate 3519 post_slice
    (by change 3519 + postTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := postTemplate) (by decide))
    (by decide)

theorem post_pc : postSite.startPC = UInt256.ofNat 4626 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3519) = UInt256.ofNat 4626
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def joinTemplate : List Instr := [.op .JUMPDEST, .op .JUMPDEST]

theorem join_slice :
    (Artifact.submissionArtifact.instructions.drop 255).take joinTemplate.length = joinTemplate := by rfl

def joinSite : GenericRoundSite Artifact.submissionArtifact .Osaka joinTemplate :=
  StackSiteBuilder.ofSlice joinTemplate 255 join_slice
    (by change 255 + joinTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := joinTemplate) (by decide))
    (by decide)

theorem join_pc : joinSite.startPC = UInt256.ofNat 485 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 255) = UInt256.ofNat 485
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 486).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 256 = 486 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 256 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 486 = true
  rw [hcode]
  exact h

def gasSteps_join (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 485, stack := rho}
      {s with pc := UInt256.ofNat 487, stack := rho} := by
  apply PadLift.gasSteps_of_raw joinSite {s with pc := UInt256.ofNat 485, stack := rho} _
    hcode hfork hrun hnp join_pc.symm
  · apply PadLift.advancesAll_sound
    decide
  · simp [joinTemplate, runInstrSeq, DataStepper.runInstr, hrun, hstack]
    rfl

def loopJoinTemplate : List Instr := [.op .JUMPDEST]

theorem loopJoin_slice :
    (Artifact.submissionArtifact.instructions.drop 256).take loopJoinTemplate.length = loopJoinTemplate := by rfl

def loopJoinSite : GenericRoundSite Artifact.submissionArtifact .Osaka loopJoinTemplate :=
  StackSiteBuilder.ofSlice loopJoinTemplate 256 loopJoin_slice
    (by change 256 + loopJoinTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := loopJoinTemplate) (by decide))
    (by decide)

theorem loopJoin_pc : loopJoinSite.startPC = UInt256.ofNat 486 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 256) = UInt256.ofNat 486
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_loop_join (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 486, stack := rho}
      {s with pc := UInt256.ofNat 487, stack := rho} := by
  apply PadLift.gasSteps_of_raw loopJoinSite {s with pc := UInt256.ofNat 486, stack := rho} _
    hcode hfork hrun hnp loopJoin_pc.symm
  · apply PadLift.advancesAll_sound
    decide
  · simp [loopJoinTemplate, runInstrSeq, DataStepper.runInstr, hrun, hstack]
    rfl

def gasSteps_continue (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hmiss : (nextOffset off).toNat < limit.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4626, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 487, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  have gp : GasSteps {s with pc := UInt256.ofNat 4626, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 486, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
    apply RecognitionLift.gasSteps_of_raw postSite {s with pc := UInt256.ofNat 4626, stack := StaggerPersistentFrame.frame h off limit rho} _ hcode hfork hrun hnp post_pc.symm
    · exact RecognitionLift.advancesAll_sound _ (by decide)
    · exact run_continue s (UInt256.ofNat 4626) h off limit rho 486 (by omega) hrun hmiss (valid_loop s hcode)
  exact gp.trans (gasSteps_loop_join s (StaggerPersistentFrame.frame h (nextOffset off) limit rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp)

def gasSteps_bound (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hhit : limit.toNat ≤ (nextOffset off).toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4626, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4638, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  apply RecognitionLift.gasSteps_of_raw postSite {s with pc := UInt256.ofNat 4626, stack := StaggerPersistentFrame.frame h off limit rho} _ hcode hfork hrun hnp post_pc.symm
  · exact RecognitionLift.advancesAll_sound _ (by decide)
  · have hr := run_exit s (UInt256.ofNat 4626) h off limit rho 486 (by omega) hrun hhit
    have he : pcAfter (UInt256.ofNat 4626) (StaggerPersistentLoopRaw.template 486) = UInt256.ofNat 4638 := by decide
    rw [he] at hr
    exact hr
def gasSteps_pad (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hbound : limit.toNat ≤ (nextOffset off).toNat)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hdispatch : s.executionEnv.calldata.size = (nextOffset off).toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4626, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4701, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  exact (gasSteps_bound s h off limit rho hstack hrun hbound hcode hfork hnp).trans
    (StaggerPersistentEntrySites.gasSteps_hit s (nextOffset off) limit h rho hstack hrun hfit hdispatch hcode hfork hnp)

def gasSteps_exit (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hbound : limit.toNat ≤ (nextOffset off).toNat)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hdispatch : s.executionEnv.calldata.size ≠ (nextOffset off).toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4626, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4645, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  exact (gasSteps_bound s h off limit rho hstack hrun hbound hcode hfork hnp).trans
    (StaggerPersistentEntrySites.gasSteps_miss s (nextOffset off) limit h rho hstack hrun hfit hdispatch hcode hfork hnp)

#print axioms gasSteps_continue
#print axioms gasSteps_exit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
