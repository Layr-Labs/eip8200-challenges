import Challenge.Ripemd160.Submission.Proofs.Bytecode.SplitJoinRaw
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

/-- Block exit `DUP13 JUMP` at 4545. -/
def dispatchCode : List Instr := StaggerPersistentLoopRaw.dispatchTemplate

theorem dispatch_slice :
    (Artifact.submissionArtifact.instructions.drop 3389).take dispatchCode.length = dispatchCode := by rfl

def dispatchSite : GenericRoundSite Artifact.submissionArtifact .Osaka dispatchCode :=
  StackSiteBuilder.ofSlice dispatchCode 3389 dispatch_slice
    (by change 3389 + dispatchCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := dispatchCode) (by decide))
    (by decide)

theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 4545 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3389) = UInt256.ofNat 4545
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def incTemplate : List Instr := StaggerPersistentLoopRaw.incTemplate

theorem inc_slice :
    (Artifact.submissionArtifact.instructions.drop 72).take incTemplate.length = incTemplate := by rfl

def incSite : GenericRoundSite Artifact.submissionArtifact .Osaka incTemplate :=
  StackSiteBuilder.ofSlice incTemplate 72 inc_slice
    (by change 72 + incTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := incTemplate) (by decide))
    (by decide)

theorem inc_pc : incSite.startPC = UInt256.ofNat 134 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 72) = UInt256.ofNat 134
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- Drop the previous continuation at 133, after the shared join has installed the next one. -/
def chainTemplate : List Instr := [.op .POP]

theorem chain_slice :
    (Artifact.submissionArtifact.instructions.drop 71).take chainTemplate.length = chainTemplate := by rfl

def chainSite : GenericRoundSite Artifact.submissionArtifact .Osaka chainTemplate :=
  StackSiteBuilder.ofSlice chainTemplate 71 chain_slice
    (by change 71 + chainTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := chainTemplate) (by decide))
    (by decide)

theorem chain_pc : chainSite.startPC = UInt256.ofNat 133 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 71) = UInt256.ofNat 133
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def glHeadCode : List Instr := StaggerPersistentLoopRaw.glHeadTemplate

theorem glHead_slice :
    (Artifact.submissionArtifact.instructions.drop 130).take glHeadCode.length = glHeadCode := by rfl

def glHeadSite : GenericRoundSite Artifact.submissionArtifact .Osaka glHeadCode :=
  StackSiteBuilder.ofSlice glHeadCode 130 glHead_slice
    (by change 130 + glHeadCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := glHeadCode) (by decide))
    (by decide)

theorem glHead_pc : glHeadSite.startPC = UInt256.ofNat 222 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 130) = UInt256.ofNat 222
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def glTestCode : List Instr := StaggerPersistentLoopRaw.glTestTemplate StaggerPersistentLoopRaw.outPC

theorem glTest_slice :
    (Artifact.submissionArtifact.instructions.drop 135).take glTestCode.length = glTestCode := by rfl

def glTestSite : GenericRoundSite Artifact.submissionArtifact .Osaka glTestCode :=
  StackSiteBuilder.ofSlice glTestCode 135 glTest_slice
    (by change 135 + glTestCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := glTestCode) (by decide))
    (by decide)

theorem glTest_pc : glTestSite.startPC = UInt256.ofNat 228 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 135) = UInt256.ofNat 228
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

theorem join_pc : joinSite.startPC = UInt256.ofNat 461 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 173) = UInt256.ofNat 461
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 461).toNat = true :=
  StaggerPersistentEntrySites.valid_loop s hcode

theorem valid_chain (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 210).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 121 = 210 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 121 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 210 = true
  rw [hcode]
  exact h

theorem valid_gl (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 222).toNat = true :=
  StaggerPersistentEntrySites.valid_gl s hcode

theorem valid_out (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat StaggerPersistentLoopRaw.outPC).toNat = true :=
  StaggerPersistentEntrySites.valid_finish s hcode

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

/-- Block exit: jump to the continuation in slot 12 with the frame unchanged. -/
def gasSteps_dispatch (s : State) (h : Compression.HashState) (off cont junk : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code cont.toNat = true)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4545, stack := junk :: StaggerPersistentFrame.frame h off cont rho}
      {s with pc := cont, stack := StaggerPersistentFrame.frame h off junk rho} := by
  apply ExitLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4545, stack := junk :: StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact ExitLift.advancesAll_sound _ (by decide)
  · exact StaggerPersistentLoopRaw.run_dispatch s (UInt256.ofNat 4545) h off cont junk rho (by omega) hrun hvalid

/-- The 192 stub pushes its next continuation before jumping to the shared join. -/
def stub192Push : GenericRoundSite Artifact.submissionArtifact .Osaka (StaggerPersistentLoopRaw.pushContTemplate 128) :=
  StackSiteBuilder.ofSlice (StaggerPersistentLoopRaw.pushContTemplate 128) 109 (by rfl)
    (by change 109 + (StaggerPersistentLoopRaw.pushContTemplate 128).length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := (StaggerPersistentLoopRaw.pushContTemplate 128)) (by decide))
    (by decide)

def glPush : GenericRoundSite Artifact.submissionArtifact .Osaka (StaggerPersistentLoopRaw.pushContTemplate 222) :=
  StackSiteBuilder.ofSlice (StaggerPersistentLoopRaw.pushContTemplate 222) 138 (by rfl)
    (by change 138 + (StaggerPersistentLoopRaw.pushContTemplate 222).length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := (StaggerPersistentLoopRaw.pushContTemplate 222)) (by decide))
    (by decide)

def joinSwapSite : GenericRoundSite Artifact.submissionArtifact .Osaka StaggerPersistentLoopRaw.joinSwapTemplate :=
  StackSiteBuilder.ofSlice StaggerPersistentLoopRaw.joinSwapTemplate 121 (by rfl)
    (by change 121 + StaggerPersistentLoopRaw.joinSwapTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := StaggerPersistentLoopRaw.joinSwapTemplate) (by decide))
    (by decide)

theorem stub128Set_slice :
    (Artifact.submissionArtifact.instructions.drop 69).take
      (StaggerPersistentLoopRaw.setContTemplate 64).length =
        StaggerPersistentLoopRaw.setContTemplate 64 := by rfl

def stub128Set : GenericRoundSite Artifact.submissionArtifact .Osaka (StaggerPersistentLoopRaw.setContTemplate 64) :=
  StackSiteBuilder.ofSlice (StaggerPersistentLoopRaw.setContTemplate 64) 69 stub128Set_slice
    (by change 69 + (StaggerPersistentLoopRaw.setContTemplate 64).length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := StaggerPersistentLoopRaw.setContTemplate 64) (by decide))
    (by decide)

theorem stub192Push_pc : stub192Push.startPC = UInt256.ofNat 193 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 109) = UInt256.ofNat 193
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem glPush_pc : glPush.startPC = UInt256.ofNat 233 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 138) = UInt256.ofNat 233
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem joinSwapSite_pc : joinSwapSite.startPC = UInt256.ofNat 210 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 121) = UInt256.ofNat 210
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem stub128Set_pc : stub128Set.startPC = UInt256.ofNat 129 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 69) = UInt256.ofNat 129
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- A single `JUMPDEST` site (the stub entries 192 and 128). -/
def jumpdestSite (idx : Nat)
    (hslice : (Artifact.submissionArtifact.instructions.drop idx).take 1 = [.op .JUMPDEST])
    (hbound : idx + 1 ≤ Artifact.submissionInstructions.length) :
    GenericRoundSite Artifact.submissionArtifact .Osaka [.op .JUMPDEST] :=
  StackSiteBuilder.ofSlice [.op .JUMPDEST] idx hslice hbound
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := [.op .JUMPDEST]) (by decide)) (by decide)

def stub192Dest := jumpdestSite 108 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)
def stub128Dest := jumpdestSite 68 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)

theorem stub192Dest_pc : stub192Dest.startPC = UInt256.ofNat 192 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 108) = UInt256.ofNat 192
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem stub128Dest_pc : stub128Dest.startPC = UInt256.ofNat 128 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 68) = UInt256.ofNat 128
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- `PUSH1 0x83 JUMP`: hop to the shared continuation join at 210. -/
def advJumpSite (idx : Nat)
    (hslice : (Artifact.submissionArtifact.instructions.drop idx).take (PadJump.template1 210).length =
      PadJump.template1 210)
    (hbound : idx + (PadJump.template1 210).length ≤ Artifact.submissionInstructions.length) :
    GenericRoundSite Artifact.submissionArtifact .Osaka (PadJump.template1 210) :=
  StackSiteBuilder.ofSlice (PadJump.template1 210) idx hslice hbound
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := PadJump.template1 210) (by decide)) (by decide)

def stub192Jump := advJumpSite 110 (by rfl) (by rw [Artifact.referenceInstructions_count]; decide)
/-- `PUSH1 0x83 JUMP` at 61: the last-block stay hops to the shared join at 210. -/
def glHopJump : GenericRoundSite Artifact.submissionArtifact .Osaka (PadJump.template1 210) :=
  StackSiteBuilder.ofSlice (PadJump.template1 210) 139 (by rfl)
    (by change 139 + (PadJump.template1 210).length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := PadJump.template1 210) (by decide)) (by decide)

theorem stub192Jump_pc : stub192Jump.startPC = UInt256.ofNat 195 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 110) = UInt256.ofNat 195
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem glHopJump_pc : glHopJump.startPC = UInt256.ofNat 235 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 139) = UInt256.ofNat 235
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

private def setCont_gasSteps (v pc : Nat)
    (site : GenericRoundSite Artifact.submissionArtifact .Osaka (StaggerPersistentLoopRaw.setContTemplate v))
    (hpc : site.startPC = UInt256.ofNat pc)
    (hadv : (StaggerPersistentLoopRaw.setContTemplate v).dropLast.all PadLift.advancesCheck = true)
    (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat pc, stack := StaggerPersistentFrame.frame h off cont rho}
      { s with
        pc := pcAfter (UInt256.ofNat pc) (StaggerPersistentLoopRaw.setContTemplate v)
        stack := cont :: StaggerPersistentFrame.frame h off (UInt256.ofNat v) rho } := by
  apply PadLift.gasSteps_of_raw site {s with pc := UInt256.ofNat pc, stack := StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp hpc.symm
  · exact PadLift.advancesAll_sound _ hadv
  · exact StaggerPersistentLoopRaw.run_setCont s (UInt256.ofNat pc) h off cont rho v (by omega) hrun

private def advJump_gasSteps
    (site : GenericRoundSite Artifact.submissionArtifact .Osaka (PadJump.template1 210))
    (pc : Nat) (hpc : site.startPC = UInt256.ofNat pc)
    (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat pc, stack := rho}
      {s with pc := UInt256.ofNat 210, stack := rho} := by
  apply PadLift.gasSteps_of_raw site {s with pc := UInt256.ofNat pc, stack := rho} _ hcode hfork hrun hnp hpc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template1 s (UInt256.ofNat pc) rho 210 (by omega) hrun
      (StaggerPersistentEntrySites.valid_adv s hcode)

theorem valid_join (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 210).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 121 = 210 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 121 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 210 = true
  rw [hcode]
  exact h

private def hopJump_gasSteps
    (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 235, stack := rho}
      {s with pc := UInt256.ofNat 210, stack := rho} := by
  apply PadLift.gasSteps_of_raw glHopJump {s with pc := UInt256.ofNat 235, stack := rho} _ hcode hfork hrun hnp glHopJump_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template1 s (UInt256.ofNat 235) rho 210 (by omega) hrun (valid_join s hcode)

private def pushCont_gasSteps (v pc : Nat)
    (site : GenericRoundSite Artifact.submissionArtifact .Osaka (StaggerPersistentLoopRaw.pushContTemplate v))
    (hpc : site.startPC = UInt256.ofNat pc)
    (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat pc, stack := StaggerPersistentFrame.frame h off cont rho}
      { s with
        pc := pcAfter (UInt256.ofNat pc) (StaggerPersistentLoopRaw.pushContTemplate v)
        stack := UInt256.ofNat v :: StaggerPersistentFrame.frame h off cont rho } := by
  apply PadLift.gasSteps_of_raw site {s with pc := UInt256.ofNat pc, stack := StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp hpc.symm
  · exact PadLift.advancesAll_sound _ (by rfl)
  · exact StaggerPersistentLoopRaw.run_pushCont s (UInt256.ofNat pc) h off cont rho v (by omega) hrun

private def joinSwap_gasSteps
    (s : State) (h : Compression.HashState) (off cont x : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 210, stack := x :: StaggerPersistentFrame.frame h off cont rho}
      { s with pc := UInt256.ofNat 212, stack := cont :: StaggerPersistentFrame.frame h off x rho } := by
  apply PadLift.gasSteps_of_raw joinSwapSite {s with pc := UInt256.ofNat 210, stack := x :: StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp joinSwapSite_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := StaggerPersistentLoopRaw.run_joinSwap s (UInt256.ofNat 210) h off cont x rho (by omega) hrun
    have he : pcAfter (UInt256.ofNat 210) StaggerPersistentLoopRaw.joinSwapTemplate = UInt256.ofNat 212 := by decide
    rw [he] at hr
    exact hr

/-- The block advance at 133: `POP`, the offset advance, the swap back and the jump to
the loop-head marker, which block preparation executes. -/
def gasSteps_advance (s : State) (h : Compression.HashState) (off cont dead : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 133, stack := dead :: StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame h (nextOffset off) cont rho} := by
  have hlen : (dead :: StaggerPersistentFrame.frame h off cont rho).length < 1024 := by
    simp [StaggerPersistentFrame.frame]; omega
  have g1 : GasSteps {s with pc := UInt256.ofNat 133, stack := dead :: StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 134, stack := StaggerPersistentFrame.frame h off cont rho} := by
    apply PadLift.gasSteps_of_raw chainSite {s with pc := UInt256.ofNat 133, stack := dead :: StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp chain_pc.symm
    · exact PadLift.advancesAll_sound _ (by decide)
    · have hlen1 : (StaggerPersistentFrame.frame h off cont rho).length + 1 < 1024 := by simpa only [List.length_cons] using hlen
      simp (discharger := omega) [hlen1, chainTemplate, runInstrSeq, DataStepper.runInstr, hrun, hlen, List.length_cons, UInt256.succ]
      rfl
  have g2 : GasSteps {s with pc := UInt256.ofNat 134, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 138, stack := StaggerPersistentFrame.exitFrame h (nextOffset off) cont rho} := by
    apply PadLift.gasSteps_of_raw incSite {s with pc := UInt256.ofNat 134, stack := StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp inc_pc.symm
    · exact PadLift.advancesAll_sound _ (by decide)
    · have hr := run_inc s (UInt256.ofNat 134) h off cont rho (by omega) hrun
      have he : pcAfter (UInt256.ofNat 134) StaggerPersistentLoopRaw.incTemplate = UInt256.ofNat 138 := by decide
      rw [he] at hr
      exact hr
  have g3 := StaggerPersistentEntrySites.gasSteps_swapBack s (nextOffset off) cont h rho hstack hrun
    hcode hfork hnp
  have g4 := StaggerPersistentEntrySites.gasSteps_back s
    (StaggerPersistentFrame.frame h (nextOffset off) cont rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp
  exact ((g1.trans g2).trans g3).trans g4

/-- The cold join clones the original swap/drop/advance path, preserving generic semantics. -/
def splitJoinSite : GenericRoundSite Artifact.submissionArtifact .Osaka SplitJoinRaw.template :=
  StackSiteBuilder.ofSlice SplitJoinRaw.template 121 (by rfl)
    (by change 121 + SplitJoinRaw.template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := SplitJoinRaw.template) (by decide)) (by decide)
theorem splitJoin_pc : splitJoinSite.startPC = UInt256.ofNat 210 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 121) = UInt256.ofNat 210
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private def splitJoin_gasSteps (s : State) (h : Compression.HashState) (off cont x : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 210, stack := x :: StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame h (nextOffset off) x rho} := by
  apply PadLift.gasSteps_of_raw splitJoinSite {s with pc := UInt256.ofNat 210, stack := x :: StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp splitJoin_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · exact SplitJoinRaw.run_template s (UInt256.ofNat 210) h off cont x rho (by omega) hrun (valid_loop s hcode)

/-- The 192 stub: the continuation becomes 128 and the block advance follows. -/
def gasSteps_stub192 (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 192, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame h (nextOffset off) (UInt256.ofNat 128) rho} := by
  have hlen : (StaggerPersistentFrame.frame h off cont rho).length < 1024 := by
    simp [StaggerPersistentFrame.frame]; omega
  have g1 := jumpdest_gasSteps stub192Dest 192 stub192Dest_pc (by norm_num) s _ hlen hrun hcode hfork hnp
  have g2 := pushCont_gasSteps 128 193 stub192Push stub192Push_pc s h off cont rho hstack hrun hcode hfork hnp
  have he : pcAfter (UInt256.ofNat 193) (StaggerPersistentLoopRaw.pushContTemplate 128) = UInt256.ofNat 195 := by decide
  rw [he] at g2
  have g3 := advJump_gasSteps stub192Jump 195 stub192Jump_pc s
    (UInt256.ofNat 128 :: StaggerPersistentFrame.frame h off cont rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp
  have g4 := splitJoin_gasSteps s h off cont (UInt256.ofNat 128) rho hstack hrun hcode hfork hnp
  exact ((g1.trans g2).trans g3).trans g4

/-- The 128 stub: the continuation becomes 64 and the block advance follows directly. -/
def gasSteps_stub128 (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 128, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 133, stack := cont :: StaggerPersistentFrame.frame h off (UInt256.ofNat 64) rho} := by
  have hlen : (StaggerPersistentFrame.frame h off cont rho).length < 1024 := by
    simp [StaggerPersistentFrame.frame]; omega
  have g1 := jumpdest_gasSteps stub128Dest 128 stub128Dest_pc (by norm_num) s _ hlen hrun hcode hfork hnp
  have g2 := setCont_gasSteps 64 129 stub128Set stub128Set_pc (by decide) s h off cont rho hstack hrun hcode hfork hnp
  have he : pcAfter (UInt256.ofNat 129) (StaggerPersistentLoopRaw.setContTemplate 64) = UInt256.ofNat 133 := by decide
  rw [he] at g2
  exact g1.trans g2

/-- The `MSIZE` at 53 (instruction 32) of the generic last-block test. -/
theorem glMsize_decoded (s : State) (stack : List UInt256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka) :
    ({s with pc := UInt256.ofNat 227, stack := stack} : State).decodedOp = some .MSIZE := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 134 .MSIZE
    (by rfl) (by decide) trivial
  apply Artifact.submissionArtifact.state_decodedOp_of ({s with pc := UInt256.ofNat 227, stack := stack} : State) 134
    hcode ?_ .MSIZE none hd (by change Operation.MSIZE.availableInFork s.fork = true; rw [hfork]; rfl)
  change (UInt256.ofNat 227).toNat = Artifact.submissionArtifact.instructionPC 134
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
    GasSteps {s with pc := UInt256.ofNat 222, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 228, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} := by
  have g1 : GasSteps {s with pc := UInt256.ofNat 222, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 227, stack := (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} := by
    apply PadLift.gasSteps_of_raw glHeadSite {s with pc := UInt256.ofNat 222, stack := StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp glHead_pc.symm
    · exact PadLift.advancesAll_sound _ (by decide)
    · have hr := StaggerPersistentLoopRaw.run_glHead s (UInt256.ofNat 222) h off cont rho (by omega) hrun
      have he : pcAfter (UInt256.ofNat 222) StaggerPersistentLoopRaw.glHeadTemplate = UInt256.ofNat 227 := by decide
      rw [he] at hr
      exact hr
  have hcap : ({s with pc := UInt256.ofNat 227, stack := (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} : State).stack.length < 1024 := by
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
    GasSteps {s with pc := UInt256.ofNat 222, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat StaggerPersistentLoopRaw.outPC, stack := StaggerPersistentFrame.frame h off cont rho} := by
  have g1 := gasSteps_glHead s h off cont rho hstack hrun hcode hfork hnp
  have g2 : GasSteps {s with pc := UInt256.ofNat 228, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat StaggerPersistentLoopRaw.outPC, stack := StaggerPersistentFrame.frame h off cont rho} := by
    apply glTest_gasSteps_of_raw {s with pc := UInt256.ofNat 228, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp glTest_pc.symm
    · exact StaggerPersistentLoopRaw.run_glExit s (UInt256.ofNat 228) _ _ _ _
        (by simp [StaggerPersistentFrame.frame]; omega) hrun hlt (valid_out s hcode)
  exact g1.trans g2

/-- The active size reaches `off + 128`: the generic route jumps to the block advance at 133. -/
def gasSteps_glStay (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hge : ¬ (UInt256.ofNat (32 * s.activeWords.toNat)).toNat < (off + UInt256.ofNat 128).toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 222, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame h (nextOffset off) (UInt256.ofNat 222) rho} := by
  have g1 := gasSteps_glHead s h off cont rho hstack hrun hcode hfork hnp
  have g2 : GasSteps {s with pc := UInt256.ofNat 228, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 233, stack := StaggerPersistentFrame.frame h off cont rho} := by
    apply glTest_gasSteps_of_raw {s with pc := UInt256.ofNat 228, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp glTest_pc.symm
    · have hr := StaggerPersistentLoopRaw.run_glStay s (UInt256.ofNat 228) (StaggerPersistentFrame.frame h off cont rho) _ _ StaggerPersistentLoopRaw.outPC
        (by simp [StaggerPersistentFrame.frame]; omega) hrun hge
      have he : pcAfter (UInt256.ofNat 228) (StaggerPersistentLoopRaw.glTestTemplate StaggerPersistentLoopRaw.outPC) = UInt256.ofNat 233 := by decide
      rw [he] at hr
      exact hr
  have g3 := pushCont_gasSteps 222 233 glPush glPush_pc s h off cont rho hstack hrun hcode hfork hnp
  have he : pcAfter (UInt256.ofNat 233) (StaggerPersistentLoopRaw.pushContTemplate 222) = UInt256.ofNat 235 := by decide
  rw [he] at g3
  have g4 := hopJump_gasSteps s (UInt256.ofNat 222 :: StaggerPersistentFrame.frame h off cont rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp
  have g5 := splitJoin_gasSteps s h off cont (UInt256.ofNat 222) rho hstack hrun hcode hfork hnp
  exact (g1.trans g2).trans ((g3.trans g4).trans g5)

#print axioms gasSteps_dispatch
#print axioms gasSteps_advance
#print axioms gasSteps_stub192
#print axioms gasSteps_stub128
#print axioms gasSteps_glExit
#print axioms gasSteps_glStay
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
