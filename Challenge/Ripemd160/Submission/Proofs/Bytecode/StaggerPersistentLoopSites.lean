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

/-- Block exit `DUP13 JUMP` at 4551. -/
def dispatchCode : List Instr := StaggerPersistentLoopRaw.dispatchTemplate

theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 3392).take dispatchCode.length = dispatchCode := by rfl

def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchCode :=
  StackSiteBuilder.ofSlice dispatchCode 3392 dispatch_slice
    (by change 3392 + dispatchCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchCode) (by decide))
    (by decide)

theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 4551 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3392) = UInt256.ofNat 4551
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def incTemplate : List Instr := StaggerPersistentLoopRaw.incTemplate

theorem inc_slice :
    (Artifact.submissionArtifact.instructions.drop 3517).take incTemplate.length = incTemplate := by rfl

def incSite : GenericRoundSite Artifact.submissionArtifact .Osaka incTemplate :=
  StackSiteBuilder.ofSlice incTemplate 3517 inc_slice
    (by change 3517 + incTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := incTemplate) (by decide))
    (by decide)

theorem inc_pc : incSite.startPC = UInt256.ofNat 4769 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3517) = UInt256.ofNat 4769
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def chainTemplate : List Instr := [.op .JUMPDEST]

theorem chain_slice :
    (Artifact.submissionArtifact.instructions.drop 3516).take chainTemplate.length = chainTemplate := by rfl

def chainSite : GenericRoundSite Artifact.submissionArtifact .Osaka chainTemplate :=
  StackSiteBuilder.ofSlice chainTemplate 3516 chain_slice
    (by change 3516 + chainTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := chainTemplate) (by decide))
    (by decide)

theorem chain_pc : chainSite.startPC = UInt256.ofNat 4768 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3516) = UInt256.ofNat 4768
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def glHeadCode : List Instr := StaggerPersistentLoopRaw.glHeadTemplate

theorem glHead_slice :
    (Artifact.submissionArtifact.instructions.drop 3508).take glHeadCode.length = glHeadCode := by rfl

def glHeadSite : GenericRoundSite Artifact.submissionArtifact .Osaka glHeadCode :=
  StackSiteBuilder.ofSlice glHeadCode 3508 glHead_slice
    (by change 3508 + glHeadCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := glHeadCode) (by decide))
    (by decide)

theorem glHead_pc : glHeadSite.startPC = UInt256.ofNat 4757 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3508) = UInt256.ofNat 4757
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def glTestCode : List Instr := StaggerPersistentLoopRaw.glTestTemplate StaggerPersistentLoopRaw.outPC

theorem glTest_slice :
    (Artifact.submissionArtifact.instructions.drop 3513).take glTestCode.length = glTestCode := by rfl

def glTestSite : GenericRoundSite Artifact.submissionArtifact .Osaka glTestCode :=
  StackSiteBuilder.ofSlice glTestCode 3513 glTest_slice
    (by change 3513 + glTestCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := glTestCode) (by decide))
    (by decide)

theorem glTest_pc : glTestSite.startPC = UInt256.ofNat 4763 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3513) = UInt256.ofNat 4763
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def joinTemplate : List Instr := [.op .JUMPDEST]

theorem join_slice :
    (Artifact.submissionArtifact.instructions.drop 173).take joinTemplate.length = joinTemplate := by rfl

def joinSite : GenericRoundSite Artifact.submissionArtifact .Osaka joinTemplate :=
  StackSiteBuilder.ofSlice joinTemplate 173 join_slice
    (by change 173 + joinTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := joinTemplate) (by decide))
    (by decide)

theorem join_pc : joinSite.startPC = UInt256.ofNat 457 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 173) = UInt256.ofNat 457
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 457).toNat = true :=
  StaggerPersistentEntrySites.valid_loop s hcode

theorem valid_chain (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 4768).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3516 = 4768 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3516 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 4768 = true
  rw [hcode]
  exact h

theorem valid_gl (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 4757).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3508 = 4757 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3508 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 4757 = true
  rw [hcode]
  exact h

theorem valid_out (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat StaggerPersistentLoopRaw.outPC).toNat = true :=
  StaggerPersistentEntrySites.valid_finish s hcode

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

/-- Block exit: jump to the continuation in slot 12 with the frame unchanged. -/
def gasSteps_dispatch (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code cont.toNat = true)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4551, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := cont, stack := StaggerPersistentFrame.frame h off cont rho} := by
  apply ExitLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4551, stack := StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact ExitLift.advancesAll_sound _ (by decide)
  · exact StaggerPersistentLoopRaw.run_dispatch s (UInt256.ofNat 4551) h off cont rho (by omega) hrun hvalid

/-- The pad-test chain at 4768 up to the pad test: `JUMPDEST`, then the offset advance. -/
def gasSteps_chainStep (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4768, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 4773, stack := StaggerPersistentFrame.exitFrame h (nextOffset off) cont rho} := by
  have g1 : GasSteps {s with pc := UInt256.ofNat 4768, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 4769, stack := StaggerPersistentFrame.frame h off cont rho} := by
    apply PadLift.gasSteps_of_raw chainSite {s with pc := UInt256.ofNat 4768, stack := StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp chain_pc.symm
    · apply PadLift.advancesAll_sound
      decide
    · simpa only [chainTemplate, show UInt256.ofNat 4768 + UInt256.ofNat 1 = UInt256.ofNat 4769 by decide] using
        PadJump.run_merge s (UInt256.ofNat 4768) (StaggerPersistentFrame.frame h off cont rho)
          (by simp [StaggerPersistentFrame.frame]; omega) hrun
  have g2 : GasSteps {s with pc := UInt256.ofNat 4769, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 4773, stack := StaggerPersistentFrame.exitFrame h (nextOffset off) cont rho} := by
    apply PadLift.gasSteps_of_raw incSite {s with pc := UInt256.ofNat 4769, stack := StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp inc_pc.symm
    · exact PadLift.advancesAll_sound _ (by decide)
    · have hr := run_inc s (UInt256.ofNat 4769) h off cont rho (by omega) hrun
      have he : pcAfter (UInt256.ofNat 4769) StaggerPersistentLoopRaw.incTemplate = UInt256.ofNat 4773 := by decide
      rw [he] at hr
      exact hr
  exact g1.trans g2

/-- Pad test missed: the advanced offset goes back into slot 11 and the loop runs the next block. -/
def gasSteps_continue (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hmiss : nextOffset off ≠ UInt256.ofNat (32 * s.activeWords.toNat))
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4768, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 458, stack := StaggerPersistentFrame.frame h (nextOffset off) cont rho} := by
  have gp := gasSteps_chainStep s h off cont rho hstack hrun hcode hfork hnp
  have g2 := StaggerPersistentEntrySites.gasSteps_padMiss s (nextOffset off) cont h rho hstack hrun
    hmiss hcode hfork hnp
  have g3 := StaggerPersistentEntrySites.gasSteps_swapBack s (nextOffset off) cont h rho hstack hrun
    hcode hfork hnp
  have g4 := StaggerPersistentEntrySites.gasSteps_back s
    (StaggerPersistentFrame.frame h (nextOffset off) cont rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp
  exact (((gp.trans g2).trans g3).trans g4).trans (gasSteps_join s (StaggerPersistentFrame.frame h (nextOffset off) cont rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp)

/-- Pad test hit: the pad-only block starts with the advanced offset still on top. -/
def gasSteps_pad (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hdispatch : nextOffset off = UInt256.ofNat (32 * s.activeWords.toNat))
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4768, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 129, stack := StaggerPersistentFrame.exitFrame h (nextOffset off) cont rho} := by
  have gp := gasSteps_chainStep s h off cont rho hstack hrun hcode hfork hnp
  exact gp.trans (StaggerPersistentEntrySites.gasSteps_padHit s (nextOffset off) cont h rho hstack hrun
    hdispatch hcode hfork hnp)

/-- The `MSIZE` at 4762 (instruction 3512) of the generic last-block test. -/
theorem glMsize_decoded (s : State) (stack : List UInt256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka) :
    ({s with pc := UInt256.ofNat 4762, stack := stack} : State).decodedOp = some .MSIZE := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3512 .MSIZE
    (by rfl) (by decide) trivial
  apply Artifact.submissionArtifact.state_decodedOp_of ({s with pc := UInt256.ofNat 4762, stack := stack} : State) 3512
    hcode ?_ .MSIZE none hd (by change Operation.MSIZE.availableInFork s.fork = true; rw [hfork]; rfl)
  change (UInt256.ofNat 4762).toNat = Artifact.submissionArtifact.instructionPC 3512
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem lt_pc {s t : State}
    (hresult : DataStepper.runInstr (.op .LT) s = some t) :
    t.pc = s.pc + UInt256.ofNat 1 := by
  by_cases hcap : s.stack.length < 1024
  · simp only [DataStepper.runInstr, if_pos hcap] at hresult
    cases hs : s.stack with
    | nil => simp [hs] at hresult
    | cons a tail =>
      cases ht : tail with
      | nil => simp [hs, ht] at hresult
      | cons b rest =>
        simp [hs, ht] at hresult
        subst t
        rfl
  · simp [DataStepper.runInstr, hcap] at hresult

/-- The generic test site ends in `JUMPI`; its two straight-line instructions are `LT` and a push. -/
private def glTest_gasSteps_of_raw (s t : State)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hpc : s.pc = glTestSite.startPC)
    (hresult : runInstrSeq glTestCode s = some t) : GasSteps s t := by
  apply DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka glTestSite.path hcode hfork
  · have hl := PairedHelperBooleanTrace.runLocatedBlock_eq_raw_terminal_sites glTestSite.sites glTestCode
      glTestSite.instruction_eq glTestSite.contiguous s
      (by rw [glTestSite.head_eq]; exact congrArg some hpc.symm) (by
        intro located hmem u v hr
        have hm : located.located.instruction ∈
            glTestSite.sites.dropLast.map (fun item => item.located.instruction) := List.mem_map_of_mem hmem
        rw [List.map_dropLast, glTestSite.instruction_eq] at hm
        simp only [glTestCode, StaggerPersistentLoopRaw.glTestTemplate, List.dropLast_cons_cons,
          List.dropLast_singleton, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
        rcases hm with h | h
        · rw [h] at hr ⊢; exact lt_pc hr
        · rw [h] at hr ⊢; exact PadLift.runInstr_pc_extra (PadLift.advancesCheck_sound _ (by decide)) hr)
    change DataStepper.runLocatedBlock (LocatedSite.path glTestSite.sites) s = some t
    rw [hl]
    exact hresult
  · exact hrun
  · exact hnp

/-- Generic last-block test up to its branch: `off + 128` and the active size on top. -/
def gasSteps_glHead (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4757, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 4763, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} := by
  have g1 : GasSteps {s with pc := UInt256.ofNat 4757, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 4762, stack := (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} := by
    apply PadLift.gasSteps_of_raw glHeadSite {s with pc := UInt256.ofNat 4757, stack := StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp glHead_pc.symm
    · exact PadLift.advancesAll_sound _ (by decide)
    · have hr := StaggerPersistentLoopRaw.run_glHead s (UInt256.ofNat 4757) h off cont rho (by omega) hrun
      have he : pcAfter (UInt256.ofNat 4757) StaggerPersistentLoopRaw.glHeadTemplate = UInt256.ofNat 4762 := by decide
      rw [he] at hr
      exact hr
  have hcap : ({s with pc := UInt256.ofNat 4762, stack := (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} : State).stack.length < 1024 := by
    change ((off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho).length < 1024
    simp [StaggerPersistentFrame.frame]; omega
  have g2 := Msize.step (glMsize_decoded s ((off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho) hcode hfork) hcap hrun hnp
  exact g1.trans (g2.cast rfl (by simp only [Word.succ_ofNat_mod]))

/-- The active size is below `off + 128`: the generic route leaves for the output. -/
def gasSteps_glExit (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hlt : (UInt256.ofNat (32 * s.activeWords.toNat)).toNat < (off + UInt256.ofNat 128).toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4757, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat StaggerPersistentLoopRaw.outPC, stack := StaggerPersistentFrame.frame h off cont rho} := by
  have g1 := gasSteps_glHead s h off cont rho hstack hrun hcode hfork hnp
  have g2 : GasSteps {s with pc := UInt256.ofNat 4763, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat StaggerPersistentLoopRaw.outPC, stack := StaggerPersistentFrame.frame h off cont rho} := by
    apply glTest_gasSteps_of_raw {s with pc := UInt256.ofNat 4763, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp glTest_pc.symm
    · exact StaggerPersistentLoopRaw.run_glExit s (UInt256.ofNat 4763) _ _ _ _
        (by simp [StaggerPersistentFrame.frame]; omega) hrun hlt (valid_out s hcode)
  exact g1.trans g2

/-- The active size reaches `off + 128`: the generic route falls into the pad-test chain. -/
def gasSteps_glStay (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hge : ¬ (UInt256.ofNat (32 * s.activeWords.toNat)).toNat < (off + UInt256.ofNat 128).toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4757, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 4768, stack := StaggerPersistentFrame.frame h off cont rho} := by
  have g1 := gasSteps_glHead s h off cont rho hstack hrun hcode hfork hnp
  have g2 : GasSteps {s with pc := UInt256.ofNat 4763, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 4768, stack := StaggerPersistentFrame.frame h off cont rho} := by
    apply glTest_gasSteps_of_raw {s with pc := UInt256.ofNat 4763, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp glTest_pc.symm
    · have hr := StaggerPersistentLoopRaw.run_glStay s (UInt256.ofNat 4763) (StaggerPersistentFrame.frame h off cont rho) _ _ StaggerPersistentLoopRaw.outPC
        (by simp [StaggerPersistentFrame.frame]; omega) hrun hge
      have he : pcAfter (UInt256.ofNat 4763) (StaggerPersistentLoopRaw.glTestTemplate StaggerPersistentLoopRaw.outPC) = UInt256.ofNat 4768 := by decide
      rw [he] at hr
      exact hr
  exact g1.trans g2

#print axioms gasSteps_dispatch
#print axioms gasSteps_continue
#print axioms gasSteps_pad
#print axioms gasSteps_glExit
#print axioms gasSteps_glStay
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
