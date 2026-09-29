import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExitLift
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentLoopRaw

def postTemplate : List Instr := StaggerPersistentLoopRaw.template 4581

theorem post_slice :
    (Artifact.submissionArtifact.instructions.drop 3421).take postTemplate.length = postTemplate := by rfl

def postSite : GenericRoundSite Artifact.submissionArtifact .Osaka postTemplate :=
  StackSiteBuilder.ofSlice postTemplate 3421 post_slice
    (by change 3421 + postTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := postTemplate) (by decide))
    (by decide)

theorem post_pc : postSite.startPC = UInt256.ofNat 4559 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3421) = UInt256.ofNat 4559
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def joinTemplate : List Instr := [.op .JUMPDEST]

theorem join_slice :
    (Artifact.submissionArtifact.instructions.drop 174).take joinTemplate.length = joinTemplate := by rfl

def joinSite : GenericRoundSite Artifact.submissionArtifact .Osaka joinTemplate :=
  StackSiteBuilder.ofSlice joinTemplate 174 join_slice
    (by change 174 + joinTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := joinTemplate) (by decide))
    (by decide)

theorem join_pc : joinSite.startPC = UInt256.ofNat 457 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 174) = UInt256.ofNat 457
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 457).toNat = true :=
  StaggerPersistentEntrySites.valid_loop s hcode

def gasSteps_join (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 457, stack := rho}
      {s with pc := UInt256.ofNat 458, stack := rho} := by
  apply PadLift.gasSteps_of_raw joinSite {s with pc := UInt256.ofNat 457, stack := rho} _
    hcode hfork hrun hnp join_pc.symm
  · apply PadLift.advancesAll_sound
    decide
  · simp [joinTemplate, runInstrSeq, DataStepper.runInstr, hrun, hstack]
    rfl

/-- Fall-through entry from the fast-entry guard: one filler `JUMPDEST`, then the loop head. -/
def fillTemplate : List Instr := [.op .JUMPDEST, .op .JUMPDEST]

theorem fill_slice :
    (Artifact.submissionArtifact.instructions.drop 173).take fillTemplate.length = fillTemplate := by rfl

def fillSite : GenericRoundSite Artifact.submissionArtifact .Osaka fillTemplate :=
  StackSiteBuilder.ofSlice fillTemplate 173 fill_slice
    (by change 173 + fillTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := fillTemplate) (by decide))
    (by decide)

theorem fill_pc : fillSite.startPC = UInt256.ofNat 456 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 173) = UInt256.ofNat 456
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_fill (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 456, stack := rho}
      {s with pc := UInt256.ofNat 458, stack := rho} := by
  apply PadLift.gasSteps_of_raw fillSite {s with pc := UInt256.ofNat 456, stack := rho} _
    hcode hfork hrun hnp fill_pc.symm
  · apply PadLift.advancesAll_sound
    decide
  · simp [fillTemplate, runInstrSeq, DataStepper.runInstr, hrun, hstack, pcAfter, Instr.size, UInt256.succ]
    all_goals rfl

private theorem next_ne_of_lt {off limit : UInt256}
    (h : (nextOffset off).toNat < limit.toNat) : nextOffset off ≠ limit := by
  intro he; rw [he] at h; exact Nat.lt_irrefl _ h

/-- Offset advance and finish test, not taken. -/
def gasSteps_step (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hle : (nextOffset off).toNat ≤ limit.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4559, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4570, stack := StaggerPersistentFrame.exitFrame h (nextOffset off) limit rho} := by
  apply ExitLift.gasSteps_of_raw postSite {s with pc := UInt256.ofNat 4559, stack := StaggerPersistentFrame.frame h off limit rho} _ hcode hfork hrun hnp post_pc.symm
  · exact ExitLift.advancesAll_sound _ (by decide)
  · have hr := run_le s (UInt256.ofNat 4559) h off limit rho 4581 (by omega) hrun hle
    have he : pcAfter (UInt256.ofNat 4559) (StaggerPersistentLoopRaw.template 4581) = UInt256.ofNat 4570 := by decide
    rw [he] at hr
    exact hr

def gasSteps_continue (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hmiss : (nextOffset off).toNat < limit.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4559, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 458, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  have gp := gasSteps_step s h off limit rho hstack hrun (Nat.le_of_lt hmiss) hcode hfork hnp
  have g2 := StaggerPersistentEntrySites.gasSteps_padMiss s (nextOffset off) limit h rho hstack hrun
    (next_ne_of_lt hmiss) hcode hfork hnp
  have g3 := StaggerPersistentEntrySites.gasSteps_back s
    (StaggerPersistentFrame.frame h (nextOffset off) limit rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp
  exact ((gp.trans g2).trans g3).trans (gasSteps_join s (StaggerPersistentFrame.frame h (nextOffset off) limit rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp)

def gasSteps_pad (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hbound : limit.toNat ≤ (nextOffset off).toNat)
    (hdispatch : nextOffset off = limit)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4559, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 129, stack := StaggerPersistentFrame.frame h (nextOffset off) limit rho} := by
  have gp := gasSteps_step s h off limit rho hstack hrun (by rw [hdispatch]) hcode hfork hnp
  exact gp.trans (StaggerPersistentEntrySites.gasSteps_padHit s (nextOffset off) limit h rho hstack hrun
    hdispatch hcode hfork hnp)

/-- Finish test taken: the output starts at the `JUMPDEST` at 4581 with the offset on top. -/
def gasSteps_exit (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hbound : limit.toNat ≤ (nextOffset off).toNat)
    (hdispatch : nextOffset off ≠ limit)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4559, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4581, stack := StaggerPersistentFrame.exitFrame h (nextOffset off) limit rho} := by
  have hgt : limit.toNat < (nextOffset off).toNat := by
    rcases Nat.lt_or_eq_of_le hbound with hl | he
    · exact hl
    · exact absurd (Word.word_ext he.symm) hdispatch
  apply ExitLift.gasSteps_of_raw postSite {s with pc := UInt256.ofNat 4559, stack := StaggerPersistentFrame.frame h off limit rho} _ hcode hfork hrun hnp post_pc.symm
  · exact ExitLift.advancesAll_sound _ (by decide)
  · exact run_gt s (UInt256.ofNat 4559) h off limit rho 4581 (by omega) hrun hgt
      (StaggerPersistentEntrySites.valid_finish s hcode)

#print axioms gasSteps_continue
#print axioms gasSteps_pad
#print axioms gasSteps_exit
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
