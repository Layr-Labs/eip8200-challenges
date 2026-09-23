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

def postTemplate : List Instr := StaggerPersistentLoopRaw.template 518

theorem post_slice :
    (Artifact.submissionArtifact.instructions.drop 3478).take postTemplate.length = postTemplate := by rfl

def postSite : GenericRoundSite Artifact.submissionArtifact .Osaka postTemplate :=
  StackSiteBuilder.ofSlice postTemplate 3478 post_slice
    (by change 3478 + postTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := postTemplate) (by decide))
    (by decide)

theorem post_pc : postSite.startPC = UInt256.ofNat 4624 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3478) = UInt256.ofNat 4624
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def joinTemplate : List Instr := [.op .JUMPDEST]

theorem join_slice :
    (Artifact.submissionArtifact.instructions.drop 229).take joinTemplate.length = joinTemplate := by rfl

def joinSite : GenericRoundSite Artifact.submissionArtifact .Osaka joinTemplate :=
  StackSiteBuilder.ofSlice joinTemplate 229 join_slice
    (by change 229 + joinTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := joinTemplate) (by decide))
    (by decide)

theorem join_pc : joinSite.startPC = UInt256.ofNat 518 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 229) = UInt256.ofNat 518
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 518).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 229 = 518 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 229 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 518 = true
  rw [hcode]
  exact h

def gasSteps_join (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 518, stack := rho}
      {s with pc := UInt256.ofNat 519, stack := rho} := by
  apply PadLift.gasSteps_of_raw joinSite {s with pc := UInt256.ofNat 518, stack := rho} _
    hcode hfork hrun hnp join_pc.symm
  · apply PadLift.advancesAll_sound
    decide
  · simp [joinTemplate, runInstrSeq, DataStepper.runInstr, hrun, hstack]
    rfl

def gasSteps_continue (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hmiss : (nextOffset off).toNat < limit.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4624, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 519, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  have gp : GasSteps {s with pc := UInt256.ofNat 4624, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 518, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
    apply RecognitionLift.gasSteps_of_raw postSite {s with pc := UInt256.ofNat 4624, stack := StaggerPersistentFrame.frame h off limit rho} _ hcode hfork hrun hnp post_pc.symm
    · exact RecognitionLift.advancesAll_sound _ (by decide)
    · exact run_continue s (UInt256.ofNat 4624) h off limit rho 518 (by omega) hrun hmiss (valid_loop s hcode)
  exact gp.trans (gasSteps_join s (StaggerPersistentFrame.frame h (nextOffset off) limit rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp)

def gasSteps_bound (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hhit : limit.toNat ≤ (nextOffset off).toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4624, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4636, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  apply RecognitionLift.gasSteps_of_raw postSite {s with pc := UInt256.ofNat 4624, stack := StaggerPersistentFrame.frame h off limit rho} _ hcode hfork hrun hnp post_pc.symm
  · exact RecognitionLift.advancesAll_sound _ (by decide)
  · have hr := run_exit s (UInt256.ofNat 4624) h off limit rho 518 (by omega) hrun hhit
    have he : pcAfter (UInt256.ofNat 4624) (StaggerPersistentLoopRaw.template 518) = UInt256.ofNat 4636 := by decide
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
    GasSteps {s with pc := UInt256.ofNat 4624, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4725, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
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
    GasSteps {s with pc := UInt256.ofNat 4624, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4643, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  exact (gasSteps_bound s h off limit rho hstack hrun hbound hcode hfork hnp).trans
    (StaggerPersistentEntrySites.gasSteps_miss s (nextOffset off) limit h rho hstack hrun hfit hdispatch hcode hfork hnp)

#print axioms gasSteps_continue
#print axioms gasSteps_exit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
