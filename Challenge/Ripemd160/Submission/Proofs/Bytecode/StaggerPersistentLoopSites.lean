import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExitLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopPreRaw
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentLoopRaw

abbrev preStack := PersistentStaggerTailBridge.preStack
abbrev result := PersistentStaggerFunctional.result

private theorem preStack_length (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) : (preStack memory h off cont rho).length = rho.length + 16 := by
  simp only [preStack, PersistentStaggerTailBridge.preStack, PersistentStaggerTailBridge.preStackQ,
    ScheduledTailRaw.stack3a, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Block exit `DUP16 JUMP` at 4537 (instruction 3387). -/
def exitSite : GenericRoundSite Artifact.submissionArtifact .Osaka LoopPreRaw.exitTemplate :=
  StackSiteBuilder.ofSlice LoopPreRaw.exitTemplate 3387 (by rfl)
    (by change 3387 + LoopPreRaw.exitTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := LoopPreRaw.exitTemplate) (by decide))
    (by decide)

theorem exit_pc : exitSite.startPC = UInt256.ofNat 4537 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3387) = UInt256.ofNat 4537
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def glTestCode : List Instr := StaggerPersistentLoopRaw.glTestTemplate StaggerPersistentLoopRaw.outPC

theorem glTest_slice :
    (Artifact.submissionArtifact.instructions.drop 34).take glTestCode.length = glTestCode := by rfl

def glTestSite : GenericRoundSite Artifact.submissionArtifact .Osaka glTestCode :=
  StackSiteBuilder.ofSlice glTestCode 34 glTest_slice
    (by change 34 + glTestCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := glTestCode) (by decide))
    (by decide)

theorem glTest_pc : glTestSite.startPC = UInt256.ofNat 54 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 34) = UInt256.ofNat 54
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 461).toNat = true :=
  StaggerPersistentEntrySites.valid_loop s hcode

theorem valid_gl (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 48).toNat = true :=
  StaggerPersistentEntrySites.valid_gl s hcode

theorem valid_out (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat StaggerPersistentLoopRaw.outPC).toNat = true :=
  StaggerPersistentEntrySites.valid_finish s hcode

/-- A single `JUMPDEST` site (the stub entries 192 and 128). -/
def jumpdestSite (idx : Nat)
    (hslice : (Artifact.submissionArtifact.instructions.drop idx).take 1 = [.op .JUMPDEST])
    (hbound : idx + 1 ≤ Artifact.submissionInstructions.length) :
    GenericRoundSite Artifact.submissionArtifact .Osaka [.op .JUMPDEST] :=
  StackSiteBuilder.ofSlice [.op .JUMPDEST] idx hslice hbound
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := [.op .JUMPDEST]) (by decide)) (by decide)

def padDest := jumpdestSite 40 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)
def stub128Dest := jumpdestSite 71 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)
def stub192Dest := jumpdestSite 112 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)
def zDest := jumpdestSite 3750 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)
def tDest := jumpdestSite 3754 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)

theorem padDest_pc : padDest.startPC = UInt256.ofNat 64 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 40) = UInt256.ofNat 64
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem stub128Dest_pc : stub128Dest.startPC = UInt256.ofNat 128 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 71) = UInt256.ofNat 128
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem stub192Dest_pc : stub192Dest.startPC = UInt256.ofNat 192 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 112) = UInt256.ofNat 192
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem zDest_pc : zDest.startPC = UInt256.ofNat 5100 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3750) = UInt256.ofNat 5100
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem tDest_pc : tDest.startPC = UInt256.ofNat 5105 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3754) = UInt256.ofNat 5105
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- The pad target's tail copy (65..73). -/
def padCopySite : GenericRoundSite Artifact.submissionArtifact .Osaka ScheduledTailFrame.copyTemplate :=
  StackSiteBuilder.ofSlice ScheduledTailFrame.copyTemplate 41 (by rfl)
    (by change 41 + ScheduledTailFrame.copyTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := ScheduledTailFrame.copyTemplate) (by decide))
    (by decide)
theorem padCopy_pc : padCopySite.startPC = UInt256.ofNat 65 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 41) = UInt256.ofNat 65
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- `PUSH1 v SWAP16 POP` sites: the 128 target (129) and `Z` (5101). -/
def setCont16Site (v idx : Nat)
    (hslice : (Artifact.submissionArtifact.instructions.drop idx).take (LoopPreRaw.setCont16Template v).length =
      LoopPreRaw.setCont16Template v)
    (hbound : idx + (LoopPreRaw.setCont16Template v).length ≤ Artifact.submissionInstructions.length)
    (hwf : StackRoundData.TemplateWellFormed (LoopPreRaw.setCont16Template v))
    (hne : LoopPreRaw.setCont16Template v ≠ []) :
    GenericRoundSite Artifact.submissionArtifact .Osaka (LoopPreRaw.setCont16Template v) :=
  StackSiteBuilder.ofSlice (LoopPreRaw.setCont16Template v) idx hslice hbound
    StackRoundData.artifact_code_bound (StackRoundData.templateWellFormed_mem hwf) hne
def stub128Set := setCont16Site 64 72 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)
  (by decide) (by decide)
def zSet := setCont16Site 128 3751 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)
  (by decide) (by decide)
theorem stub128Set_pc : stub128Set.startPC = UInt256.ofNat 129 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 72) = UInt256.ofNat 129
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem zSet_pc : zSet.startPC = UInt256.ofNat 5101 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3751) = UInt256.ofNat 5101
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- `PUSH2 dest JUMP` sites: the last-block stay (59), the 128 target (133), the 192 target (193). -/
def jump2Site (dest idx : Nat)
    (hslice : (Artifact.submissionArtifact.instructions.drop idx).take (PadJump.template dest).length =
      PadJump.template dest)
    (hbound : idx + (PadJump.template dest).length ≤ Artifact.submissionInstructions.length)
    (hwf : StackRoundData.TemplateWellFormed (PadJump.template dest))
    (hne : PadJump.template dest ≠ []) :
    GenericRoundSite Artifact.submissionArtifact .Osaka (PadJump.template dest) :=
  StackSiteBuilder.ofSlice (PadJump.template dest) idx hslice hbound
    StackRoundData.artifact_code_bound (StackRoundData.templateWellFormed_mem hwf) hne
def glStayJump := jump2Site 5105 37 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)
  (by decide) (by decide)
def stub128Jump := jump2Site 5105 75 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)
  (by decide) (by decide)
def stub192Jump := jump2Site 5100 113 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)
  (by decide) (by decide)
theorem glStayJump_pc : glStayJump.startPC = UInt256.ofNat 59 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 37) = UInt256.ofNat 59
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem stub128Jump_pc : stub128Jump.startPC = UInt256.ofNat 133 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 75) = UInt256.ofNat 133
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem stub192Jump_pc : stub192Jump.startPC = UInt256.ofNat 193 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 113) = UInt256.ofNat 193
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- The shared continuation `T` after its `JUMPDEST` (5106..5123). -/
def advanceSite : GenericRoundSite Artifact.submissionArtifact .Osaka LoopPreRaw.advanceTemplate :=
  StackSiteBuilder.ofSlice LoopPreRaw.advanceTemplate 3755 (by rfl)
    (by change 3755 + LoopPreRaw.advanceTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := LoopPreRaw.advanceTemplate) (by decide))
    (by decide)
theorem advance_pc : advanceSite.startPC = UInt256.ofNat 5106 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3755) = UInt256.ofNat 5106
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- The generic last-block test head (48..52). -/
def glHeadSite : GenericRoundSite Artifact.submissionArtifact .Osaka LoopPreRaw.glHead16Template :=
  StackSiteBuilder.ofSlice LoopPreRaw.glHead16Template 29 (by rfl)
    (by change 29 + LoopPreRaw.glHead16Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := LoopPreRaw.glHead16Template) (by decide))
    (by decide)
theorem glHead_pc : glHeadSite.startPC = UInt256.ofNat 48 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 29) = UInt256.ofNat 48
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

private def jumpdest_gasSteps (site : GenericRoundSite Artifact.submissionArtifact .Osaka [.op .JUMPDEST])
    (pc : Nat) (hpc : site.startPC = UInt256.ofNat pc) (hpc1 : pc + 1 < 2 ^ 256)
    (s : State) (rho : List UInt256) (hstack : rho.length < 1024) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat pc, stack := rho}
      {s with pc := UInt256.ofNat (pc + 1), stack := rho} := by
  apply PadLift.gasSteps_of_raw site {s with pc := UInt256.ofNat pc, stack := rho} _ hcode hfork hrun hnp hpc.symm
  · apply PadLift.advancesAll_sound
    decide
  · have h := PadJump.run_merge s (UInt256.ofNat pc) rho hstack hrun
    rw [show UInt256.ofNat pc + UInt256.ofNat 1 = UInt256.ofNat (pc + 1) from Word.ofNat_add_ofNat hpc1] at h
    exact h


def joinTemplate : List Instr := [.op .JUMPDEST]

theorem join_slice :
    (Artifact.submissionArtifact.instructions.drop 179).take joinTemplate.length = joinTemplate := by rfl

def joinSite : GenericRoundSite Artifact.submissionArtifact .Osaka joinTemplate :=
  StackSiteBuilder.ofSlice joinTemplate 179 join_slice
    (by change 179 + joinTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := joinTemplate) (by decide))
    (by decide)

theorem join_pc : joinSite.startPC = UInt256.ofNat 461 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 179) = UInt256.ofNat 461
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_join (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 461, stack := rho}
      {s with pc := UInt256.ofNat 462, stack := rho} := by
  apply PadLift.gasSteps_of_raw joinSite {s with pc := UInt256.ofNat 461, stack := rho} _
    hcode hfork hrun hnp join_pc.symm
  · apply PadLift.advancesAll_sound
    decide
  · simp [joinTemplate, runInstrSeq, DataStepper.runInstr, hrun, hstack]
    rfl

/-! ## The gas-accounted steps -/

def gasSteps_exit (s : State) (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code cont.toNat = true)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4537, stack := preStack memory h off cont rho}
      {s with pc := cont, stack := preStack memory h off cont rho} := by
  apply ExitLift.gasSteps_of_raw exitSite {s with pc := UInt256.ofNat 4537, stack := preStack memory h off cont rho} _ hcode hfork hrun hnp exit_pc.symm
  · exact ExitLift.advancesAll_sound _ (by decide)
  · exact LoopPreRaw.run_exit s (UInt256.ofNat 4537) memory h off cont rho (by omega) hrun hvalid

private def setCont16_gasSteps (v pc : Nat)
    (site : GenericRoundSite Artifact.submissionArtifact .Osaka (LoopPreRaw.setCont16Template v))
    (hpc : site.startPC = UInt256.ofNat pc)
    (hadv : (LoopPreRaw.setCont16Template v).dropLast.all PadLift.advancesCheck = true)
    (s : State) (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat pc, stack := preStack memory h off cont rho}
      {s with pc := pcAfter (UInt256.ofNat pc) (LoopPreRaw.setCont16Template v), stack := preStack memory h off (UInt256.ofNat v) rho} := by
  apply PadLift.gasSteps_of_raw site {s with pc := UInt256.ofNat pc, stack := preStack memory h off cont rho} _ hcode hfork hrun hnp hpc.symm
  · exact PadLift.advancesAll_sound _ hadv
  · exact LoopPreRaw.run_setCont16 s (UInt256.ofNat pc) memory h off cont rho v (by omega) hrun

private def jump2_gasSteps (dest pc : Nat)
    (site : GenericRoundSite Artifact.submissionArtifact .Osaka (PadJump.template dest))
    (hpc : site.startPC = UInt256.ofNat pc)
    (hadv : (PadJump.template dest).dropLast.all PadLift.advancesCheck = true)
    (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat dest).toNat = true)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat pc, stack := rho}
      {s with pc := UInt256.ofNat dest, stack := rho} := by
  apply PadLift.gasSteps_of_raw site {s with pc := UInt256.ofNat pc, stack := rho} _ hcode hfork hrun hnp hpc.symm
  · exact PadLift.advancesAll_sound _ hadv
  · exact PadJump.run_template s (UInt256.ofNat pc) rho dest (by omega) hrun hvalid

/-- `T` (5105): finish the tail, advance the offset, go to the loop head. -/
def gasSteps_advance (s : State) (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 5105, stack := preStack memory h off cont rho}
      {s with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame (result memory h) (nextOffset off) cont rho} := by
  have g1 := jumpdest_gasSteps tDest 5105 tDest_pc (by norm_num) s (preStack memory h off cont rho)
    (by rw [preStack_length]; omega) hrun hcode hfork hnp
  have g2 : GasSteps {s with pc := UInt256.ofNat 5106, stack := preStack memory h off cont rho}
      {s with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame (result memory h) (nextOffset off) cont rho} := by
    apply ExitLift.gasSteps_of_raw advanceSite {s with pc := UInt256.ofNat 5106, stack := preStack memory h off cont rho} _ hcode hfork hrun hnp advance_pc.symm
    · exact ExitLift.advancesAll_sound _ (by decide)
    · exact LoopPreRaw.run_advance s (UInt256.ofNat 5106) memory h off cont rho hstack hrun (valid_loop s hcode)
  exact g1.trans g2

/-- The pad target (64): the tail copy completes the previous block's frame at 74. -/
def gasSteps_padEntry (s : State) (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 64, stack := preStack memory h off cont rho}
      {s with pc := UInt256.ofNat 74, stack := StaggerPersistentFrame.frame (result memory h) off cont rho} := by
  have g1 := jumpdest_gasSteps padDest 64 padDest_pc (by norm_num) s (preStack memory h off cont rho)
    (by rw [preStack_length]; omega) hrun hcode hfork hnp
  have g2 : GasSteps {s with pc := UInt256.ofNat 65, stack := preStack memory h off cont rho}
      {s with pc := UInt256.ofNat 74, stack := StaggerPersistentFrame.frame (result memory h) off cont rho} := by
    apply PadLift.gasSteps_of_raw padCopySite {s with pc := UInt256.ofNat 65, stack := preStack memory h off cont rho} _ hcode hfork hrun hnp padCopy_pc.symm
    · exact PadLift.advancesAll_sound _ (by decide)
    · have hr := LoopPreRaw.run_padCopy s (UInt256.ofNat 65) memory h off cont rho (by omega) hrun
      have he : pcAfter (UInt256.ofNat 65) ScheduledTailFrame.copyTemplate = UInt256.ofNat 74 := by decide
      rw [he] at hr
      exact hr
  exact g1.trans g2

/-- The 128 target: the continuation becomes 64 and `T` follows. -/
def gasSteps_stub128 (s : State) (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 128, stack := preStack memory h off cont rho}
      {s with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame (result memory h) (nextOffset off) (UInt256.ofNat 64) rho} := by
  have g1 := jumpdest_gasSteps stub128Dest 128 stub128Dest_pc (by norm_num) s (preStack memory h off cont rho)
    (by rw [preStack_length]; omega) hrun hcode hfork hnp
  have g2 := setCont16_gasSteps 64 129 stub128Set stub128Set_pc (by decide) s memory h off cont rho hstack hrun hcode hfork hnp
  have he : pcAfter (UInt256.ofNat 129) (LoopPreRaw.setCont16Template 64) = UInt256.ofNat 133 := by decide
  rw [he] at g2
  have g3 := jump2_gasSteps 5105 133 stub128Jump stub128Jump_pc (by decide) s (preStack memory h off (UInt256.ofNat 64) rho)
    (by rw [preStack_length]; omega) hrun (StaggerPersistentEntrySites.valid_advance s hcode) hcode hfork hnp
  have g4 := gasSteps_advance s memory h off (UInt256.ofNat 64) rho hstack hrun hcode hfork hnp
  exact ((g1.trans g2).trans g3).trans g4

/-- The 192 target: jump to `Z`, the continuation becomes 128, and `T` follows. -/
def gasSteps_stub192 (s : State) (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 192, stack := preStack memory h off cont rho}
      {s with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame (result memory h) (nextOffset off) (UInt256.ofNat 128) rho} := by
  have hl : (preStack memory h off cont rho).length ≤ 1000 := by rw [preStack_length]; omega
  have g1 := jumpdest_gasSteps stub192Dest 192 stub192Dest_pc (by norm_num) s (preStack memory h off cont rho)
    (by omega) hrun hcode hfork hnp
  have g2 := jump2_gasSteps 5100 193 stub192Jump stub192Jump_pc (by decide) s (preStack memory h off cont rho)
    hl hrun (StaggerPersistentEntrySites.valid_cont192 s hcode) hcode hfork hnp
  have g3 := jumpdest_gasSteps zDest 5100 zDest_pc (by norm_num) s (preStack memory h off cont rho)
    (by omega) hrun hcode hfork hnp
  have g4 := setCont16_gasSteps 128 5101 zSet zSet_pc (by decide) s memory h off cont rho hstack hrun hcode hfork hnp
  have he : pcAfter (UInt256.ofNat 5101) (LoopPreRaw.setCont16Template 128) = UInt256.ofNat 5105 := by decide
  rw [he] at g4
  have g5 := gasSteps_advance s memory h off (UInt256.ofNat 128) rho hstack hrun hcode hfork hnp
  exact (((g1.trans g2).trans g3).trans g4).trans g5

/-- The `MSIZE` at 53 (instruction 32) of the generic last-block test. -/
theorem glMsize_decoded (s : State) (stack : List UInt256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka) :
    ({s with pc := UInt256.ofNat 53, stack := stack} : State).decodedOp = some .MSIZE := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 33 .MSIZE
    (by rfl) (by decide) trivial
  apply Artifact.submissionArtifact.state_decodedOp_of ({s with pc := UInt256.ofNat 53, stack := stack} : State) 33
    hcode ?_ .MSIZE none hd (by change Operation.MSIZE.availableInFork s.fork = true; rw [hfork]; rfl)
  change (UInt256.ofNat 53).toNat = Artifact.submissionArtifact.instructionPC 33
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
def gasSteps_glHead (s : State) (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 48, stack := preStack memory h off cont rho}
      {s with pc := UInt256.ofNat 54, stack := UInt256.ofNat (32 * s.activeWords.toNat) :: (off + UInt256.ofNat 128) :: preStack memory h off cont rho} := by
  have g1 : GasSteps {s with pc := UInt256.ofNat 48, stack := preStack memory h off cont rho}
      {s with pc := UInt256.ofNat 53, stack := (off + UInt256.ofNat 128) :: preStack memory h off cont rho} := by
    apply PadLift.gasSteps_of_raw glHeadSite {s with pc := UInt256.ofNat 48, stack := preStack memory h off cont rho} _ hcode hfork hrun hnp glHead_pc.symm
    · exact PadLift.advancesAll_sound _ (by decide)
    · have hr := LoopPreRaw.run_glHead16 s (UInt256.ofNat 48) memory h off cont rho (by omega) hrun
      have he : pcAfter (UInt256.ofNat 48) LoopPreRaw.glHead16Template = UInt256.ofNat 53 := by decide
      rw [he] at hr
      exact hr
  have hcap : ({s with pc := UInt256.ofNat 53, stack := (off + UInt256.ofNat 128) :: preStack memory h off cont rho} : State).stack.length < 1024 := by
    change ((off + UInt256.ofNat 128) :: preStack memory h off cont rho).length < 1024
    rw [List.length_cons, preStack_length]; omega
  have g2 := Msize.step (glMsize_decoded s ((off + UInt256.ofNat 128) :: preStack memory h off cont rho) hcode hfork) hcap hrun hnp
  exact g1.trans (g2.cast rfl (by simp only [Word.succ_ofNat_mod]))

/-- The active size is below `off + 128`: the generic route leaves for the output. -/
def gasSteps_glExit (s : State) (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hlt : (UInt256.ofNat (32 * s.activeWords.toNat)).toNat < (off + UInt256.ofNat 128).toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 48, stack := preStack memory h off cont rho}
      {s with pc := UInt256.ofNat StaggerPersistentLoopRaw.outPC, stack := preStack memory h off cont rho} := by
  have g1 := gasSteps_glHead s memory h off cont rho hstack hrun hcode hfork hnp
  have g2 : GasSteps {s with pc := UInt256.ofNat 54, stack := UInt256.ofNat (32 * s.activeWords.toNat) :: (off + UInt256.ofNat 128) :: preStack memory h off cont rho}
      {s with pc := UInt256.ofNat StaggerPersistentLoopRaw.outPC, stack := preStack memory h off cont rho} := by
    apply glTest_gasSteps_of_raw {s with pc := UInt256.ofNat 54, stack := UInt256.ofNat (32 * s.activeWords.toNat) :: (off + UInt256.ofNat 128) :: preStack memory h off cont rho} _ hcode hfork hrun hnp glTest_pc.symm
    · exact StaggerPersistentLoopRaw.run_glExit s (UInt256.ofNat 54) _ _ _ _
        (by rw [preStack_length]; omega) hrun hlt (valid_out s hcode)
  exact g1.trans g2

/-- The active size reaches `off + 128`: the generic route goes to `T` with its continuation 48. -/
def gasSteps_glStay (s : State) (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hge : ¬ (UInt256.ofNat (32 * s.activeWords.toNat)).toNat < (off + UInt256.ofNat 128).toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 48, stack := preStack memory h off cont rho}
      {s with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame (result memory h) (nextOffset off) cont rho} := by
  have g1 := gasSteps_glHead s memory h off cont rho hstack hrun hcode hfork hnp
  have g2 : GasSteps {s with pc := UInt256.ofNat 54, stack := UInt256.ofNat (32 * s.activeWords.toNat) :: (off + UInt256.ofNat 128) :: preStack memory h off cont rho}
      {s with pc := UInt256.ofNat 59, stack := preStack memory h off cont rho} := by
    apply glTest_gasSteps_of_raw {s with pc := UInt256.ofNat 54, stack := UInt256.ofNat (32 * s.activeWords.toNat) :: (off + UInt256.ofNat 128) :: preStack memory h off cont rho} _ hcode hfork hrun hnp glTest_pc.symm
    · have hr := StaggerPersistentLoopRaw.run_glStay s (UInt256.ofNat 54) (preStack memory h off cont rho) _ _ StaggerPersistentLoopRaw.outPC
        (by rw [preStack_length]; omega) hrun hge
      have he : pcAfter (UInt256.ofNat 54) (StaggerPersistentLoopRaw.glTestTemplate StaggerPersistentLoopRaw.outPC) = UInt256.ofNat 59 := by decide
      rw [he] at hr
      exact hr
  have g3 := jump2_gasSteps 5105 59 glStayJump glStayJump_pc (by decide) s (preStack memory h off cont rho)
    (by rw [preStack_length]; omega) hrun (StaggerPersistentEntrySites.valid_advance s hcode) hcode hfork hnp
  have g4 := gasSteps_advance s memory h off cont rho hstack hrun hcode hfork hnp
  exact ((g1.trans g2).trans g3).trans g4

#print axioms gasSteps_exit
#print axioms gasSteps_advance
#print axioms gasSteps_padEntry
#print axioms gasSteps_stub192
#print axioms gasSteps_stub128
#print axioms gasSteps_glExit
#print axioms gasSteps_glStay
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
