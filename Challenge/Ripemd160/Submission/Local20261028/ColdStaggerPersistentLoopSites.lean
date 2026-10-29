import Challenge.Ripemd160.Submission.Proofs.Bytecode.SplitJoinRaw
import Challenge.Ripemd160.Submission.Local20261028.ColdStaggerPersistentEntrySites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Local20261028.ColdLoopRaw
import Challenge.Ripemd160.Submission.Local20261028.ColdCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExitLift
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.StaggerPersistentLoopSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Control.LoopRaw

/-- Block exit `DUP13 JUMP` at 4545. -/
def dispatchCode : List Instr := Control.LoopRaw.dispatchTemplate

theorem dispatch_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 3345).take dispatchCode.length = dispatchCode := by rfl

def dispatchSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka dispatchCode :=
  StackSiteBuilder.ofSlice dispatchCode 3345 dispatch_slice
    (by change 3345 + dispatchCode.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check dispatchCode (by decide))
    (by decide)

theorem dispatch_pc : dispatchSite.startPC = UInt256.ofNat 4578 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 3345) = UInt256.ofNat 4578
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def incTemplate : List Instr := Control.LoopRaw.incTemplate

theorem inc_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 75).take incTemplate.length = incTemplate := by rfl

def incSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka incTemplate :=
  StackSiteBuilder.ofSlice incTemplate 75 inc_slice
    (by change 75 + incTemplate.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check incTemplate (by decide))
    (by decide)

theorem inc_pc : incSite.startPC = UInt256.ofNat 134 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 75) = UInt256.ofNat 134
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- Drop the previous continuation at 133, after the shared join has installed the next one. -/
def chainTemplate : List Instr := [.op .POP]

theorem chain_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 74).take chainTemplate.length = chainTemplate := by rfl

def chainSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka chainTemplate :=
  StackSiteBuilder.ofSlice chainTemplate 74 chain_slice
    (by change 74 + chainTemplate.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check chainTemplate (by decide))
    (by decide)

theorem chain_pc : chainSite.startPC = UInt256.ofNat 133 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 74) = UInt256.ofNat 133
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def glHeadCode : List Instr := Control.LoopRaw.glHeadTemplate

theorem glHead_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 115).take glHeadCode.length = glHeadCode := by rfl

def glHeadSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka glHeadCode :=
  StackSiteBuilder.ofSlice glHeadCode 115 glHead_slice
    (by change 115 + glHeadCode.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check glHeadCode (by decide))
    (by decide)

theorem glHead_pc : glHeadSite.startPC = UInt256.ofNat 222 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 115) = UInt256.ofNat 222
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def glTestCode : List Instr := Control.LoopRaw.glTestTemplate Control.LoopRaw.outPC

theorem glTest_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 120).take glTestCode.length = glTestCode := by rfl

def glTestSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka glTestCode :=
  StackSiteBuilder.ofSlice glTestCode 120 glTest_slice
    (by change 120 + glTestCode.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check glTestCode (by decide))
    (by decide)

theorem glTest_pc : glTestSite.startPC = UInt256.ofNat 228 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 120) = UInt256.ofNat 228
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def joinTemplate : List Instr := [.op .JUMPDEST]

theorem join_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 158).take joinTemplate.length = joinTemplate := by rfl

def joinSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka joinTemplate :=
  StackSiteBuilder.ofSlice joinTemplate 158 join_slice
    (by change 158 + joinTemplate.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check joinTemplate (by decide))
    (by decide)

theorem join_pc : joinSite.startPC = UInt256.ofNat 461 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 158) = UInt256.ofNat 461
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 461).toNat = true :=
  Control.StaggerPersistentEntrySites.valid_loop s hcode

theorem valid_chain (s : State) (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 210).toNat = true := by
  have hpc : Control.Artifact.submissionArtifact.instructionPC 106 = 210 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Control.Artifact.submissionArtifact.isValidJumpDest_index 106 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 210 = true
  rw [hcode]
  exact h

theorem valid_gl (s : State) (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 222).toNat = true :=
  Control.StaggerPersistentEntrySites.valid_gl s hcode

theorem valid_out (s : State) (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat Control.LoopRaw.outPC).toNat = true :=
  Control.StaggerPersistentEntrySites.valid_finish s hcode

def gasSteps_join (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
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
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4578, stack := junk :: StaggerPersistentFrame.frame h off cont rho}
      {s with pc := cont, stack := StaggerPersistentFrame.frame h off junk rho} := by
  apply ExitLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4578, stack := junk :: StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp dispatch_pc.symm
  · exact ExitLift.advancesAll_sound _ (by decide)
  · exact Control.LoopRaw.run_dispatch s (UInt256.ofNat 4578) h off cont junk rho (by omega) hrun hvalid

/-- The 192 stub pushes its next continuation before jumping to the shared join. -/
def stub192Push : GenericRoundSite Control.Artifact.submissionArtifact .Osaka (Control.LoopRaw.pushContTemplate 128) :=
  StackSiteBuilder.ofSlice (Control.LoopRaw.pushContTemplate 128) 94 (by rfl)
    (by change 94 + (Control.LoopRaw.pushContTemplate 128).length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := (Control.LoopRaw.pushContTemplate 128)) (by decide))
    (by decide)

def glPush : GenericRoundSite Control.Artifact.submissionArtifact .Osaka (Control.LoopRaw.pushContTemplate 222) :=
  StackSiteBuilder.ofSlice (Control.LoopRaw.pushContTemplate 222) 123 (by rfl)
    (by change 123 + (Control.LoopRaw.pushContTemplate 222).length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := (Control.LoopRaw.pushContTemplate 222)) (by decide))
    (by decide)

def joinSwapSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka Control.LoopRaw.joinSwapTemplate :=
  StackSiteBuilder.ofSlice Control.LoopRaw.joinSwapTemplate 106 (by rfl)
    (by change 106 + Control.LoopRaw.joinSwapTemplate.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check Control.LoopRaw.joinSwapTemplate (by decide))
    (by decide)

theorem stub128Set_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 72).take
      (Control.LoopRaw.setContTemplate 64).length =
        Control.LoopRaw.setContTemplate 64 := by rfl

def stub128Set : GenericRoundSite Control.Artifact.submissionArtifact .Osaka (Control.LoopRaw.setContTemplate 64) :=
  StackSiteBuilder.ofSlice (Control.LoopRaw.setContTemplate 64) 72 stub128Set_slice
    (by change 72 + (Control.LoopRaw.setContTemplate 64).length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := Control.LoopRaw.setContTemplate 64) (by decide))
    (by decide)

theorem stub192Push_pc : stub192Push.startPC = UInt256.ofNat 193 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 94) = UInt256.ofNat 193
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem glPush_pc : glPush.startPC = UInt256.ofNat 233 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 123) = UInt256.ofNat 233
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem joinSwapSite_pc : joinSwapSite.startPC = UInt256.ofNat 210 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 106) = UInt256.ofNat 210
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem stub128Set_pc : stub128Set.startPC = UInt256.ofNat 129 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 72) = UInt256.ofNat 129
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- A single `JUMPDEST` site (the stub entries 192 and 128). -/
def jumpdestSite (idx : Nat)
    (hslice : (Control.Artifact.submissionArtifact.instructions.drop idx).take 1 = [.op .JUMPDEST])
    (hbound : idx + 1 ≤ Control.Artifact.submissionInstructions.length) :
    GenericRoundSite Control.Artifact.submissionArtifact .Osaka [.op .JUMPDEST] :=
  StackSiteBuilder.ofSlice [.op .JUMPDEST] idx hslice hbound
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := [.op .JUMPDEST]) (by decide)) (by decide)

def stub192Dest := jumpdestSite 93 (by rfl) (by rw [CandidateArtifact.instruction_count]; decide)
def stub128Dest := jumpdestSite 71 (by rfl) (by rw [CandidateArtifact.instruction_count]; decide)

theorem stub192Dest_pc : stub192Dest.startPC = UInt256.ofNat 192 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 93) = UInt256.ofNat 192
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem stub128Dest_pc : stub128Dest.startPC = UInt256.ofNat 128 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 71) = UInt256.ofNat 128
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- `PUSH1 0x83 JUMP`: hop to the shared continuation join at 210. -/
def advJumpSite (idx : Nat)
    (hslice : (Control.Artifact.submissionArtifact.instructions.drop idx).take (PadJump.template1 210).length =
      PadJump.template1 210)
    (hbound : idx + (PadJump.template1 210).length ≤ Control.Artifact.submissionInstructions.length) :
    GenericRoundSite Control.Artifact.submissionArtifact .Osaka (PadJump.template1 210) :=
  StackSiteBuilder.ofSlice (PadJump.template1 210) idx hslice hbound
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := PadJump.template1 210) (by decide)) (by decide)

def stub192Jump := advJumpSite 95 (by rfl) (by rw [CandidateArtifact.instruction_count]; decide)
/-- `PUSH1 0x83 JUMP` at 61: the last-block stay hops to the shared join at 210. -/
def glHopJump : GenericRoundSite Control.Artifact.submissionArtifact .Osaka (PadJump.template1 210) :=
  StackSiteBuilder.ofSlice (PadJump.template1 210) 124 (by rfl)
    (by change 124 + (PadJump.template1 210).length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (Control.StackRoundData.templateWellFormed_mem (instructions := PadJump.template1 210) (by decide)) (by decide)

theorem stub192Jump_pc : stub192Jump.startPC = UInt256.ofNat 195 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 95) = UInt256.ofNat 195
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem glHopJump_pc : glHopJump.startPC = UInt256.ofNat 235 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 124) = UInt256.ofNat 235
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

private def jumpdest_gasSteps (site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka [.op .JUMPDEST])
    (pc : Nat) (hpc : site.startPC = UInt256.ofNat pc) (hpc1 : pc + 1 < 2 ^ 256)
    (s : State) (rho : List UInt256) (hstack : rho.length < 1024) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
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
    (site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka (Control.LoopRaw.setContTemplate v))
    (hpc : site.startPC = UInt256.ofNat pc)
    (hadv : (Control.LoopRaw.setContTemplate v).dropLast.all PadLift.advancesCheck = true)
    (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat pc, stack := StaggerPersistentFrame.frame h off cont rho}
      { s with
        pc := pcAfter (UInt256.ofNat pc) (Control.LoopRaw.setContTemplate v)
        stack := cont :: StaggerPersistentFrame.frame h off (UInt256.ofNat v) rho } := by
  apply PadLift.gasSteps_of_raw site {s with pc := UInt256.ofNat pc, stack := StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp hpc.symm
  · exact PadLift.advancesAll_sound _ hadv
  · exact Control.LoopRaw.run_setCont s (UInt256.ofNat pc) h off cont rho v (by omega) hrun

private def advJump_gasSteps
    (site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka (PadJump.template1 210))
    (pc : Nat) (hpc : site.startPC = UInt256.ofNat pc)
    (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat pc, stack := rho}
      {s with pc := UInt256.ofNat 210, stack := rho} := by
  apply PadLift.gasSteps_of_raw site {s with pc := UInt256.ofNat pc, stack := rho} _ hcode hfork hrun hnp hpc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template1 s (UInt256.ofNat pc) rho 210 (by omega) hrun
      (Control.StaggerPersistentEntrySites.valid_adv s hcode)

theorem valid_join (s : State) (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 210).toNat = true := by
  have hpc : Control.Artifact.submissionArtifact.instructionPC 106 = 210 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Control.Artifact.submissionArtifact.isValidJumpDest_index 106 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 210 = true
  rw [hcode]
  exact h

private def hopJump_gasSteps
    (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 235, stack := rho}
      {s with pc := UInt256.ofNat 210, stack := rho} := by
  apply PadLift.gasSteps_of_raw glHopJump {s with pc := UInt256.ofNat 235, stack := rho} _ hcode hfork hrun hnp glHopJump_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template1 s (UInt256.ofNat 235) rho 210 (by omega) hrun (valid_join s hcode)

private def pushCont_gasSteps (v pc : Nat)
    (site : GenericRoundSite Control.Artifact.submissionArtifact .Osaka (Control.LoopRaw.pushContTemplate v))
    (hpc : site.startPC = UInt256.ofNat pc)
    (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat pc, stack := StaggerPersistentFrame.frame h off cont rho}
      { s with
        pc := pcAfter (UInt256.ofNat pc) (Control.LoopRaw.pushContTemplate v)
        stack := UInt256.ofNat v :: StaggerPersistentFrame.frame h off cont rho } := by
  apply PadLift.gasSteps_of_raw site {s with pc := UInt256.ofNat pc, stack := StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp hpc.symm
  · exact PadLift.advancesAll_sound _ (by rfl)
  · exact Control.LoopRaw.run_pushCont s (UInt256.ofNat pc) h off cont rho v (by omega) hrun

private def joinSwap_gasSteps
    (s : State) (h : Compression.HashState) (off cont x : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 210, stack := x :: StaggerPersistentFrame.frame h off cont rho}
      { s with pc := UInt256.ofNat 212, stack := cont :: StaggerPersistentFrame.frame h off x rho } := by
  apply PadLift.gasSteps_of_raw joinSwapSite {s with pc := UInt256.ofNat 210, stack := x :: StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp joinSwapSite_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := Control.LoopRaw.run_joinSwap s (UInt256.ofNat 210) h off cont x rho (by omega) hrun
    have he : pcAfter (UInt256.ofNat 210) Control.LoopRaw.joinSwapTemplate = UInt256.ofNat 212 := by decide
    rw [he] at hr
    exact hr

/-- The block advance at 133: `POP`, the offset advance, the swap back and the jump to
the loop-head marker, which block preparation executes. -/
def gasSteps_advance (s : State) (h : Compression.HashState) (off cont dead : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
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
      have he : pcAfter (UInt256.ofNat 134) Control.LoopRaw.incTemplate = UInt256.ofNat 138 := by decide
      rw [he] at hr
      exact hr
  have g3 := Control.StaggerPersistentEntrySites.gasSteps_swapBack s (nextOffset off) cont h rho hstack hrun
    hcode hfork hnp
  have g4 := Control.StaggerPersistentEntrySites.gasSteps_back s
    (StaggerPersistentFrame.frame h (nextOffset off) cont rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp
  exact ((g1.trans g2).trans g3).trans g4

/-- The cold join clones the original swap/drop/advance path, preserving generic semantics. -/
def splitJoinSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka SplitJoinRaw.template :=
  StackSiteBuilder.ofSlice SplitJoinRaw.template 106 (by rfl)
    (by change 106 + SplitJoinRaw.template.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check SplitJoinRaw.template (by decide)) (by decide)
theorem splitJoin_pc : splitJoinSite.startPC = UInt256.ofNat 210 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 106) = UInt256.ofNat 210
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private def splitJoin_gasSteps (s : State) (h : Compression.HashState) (off cont x : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
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
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 192, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 461, stack := StaggerPersistentFrame.frame h (nextOffset off) (UInt256.ofNat 128) rho} := by
  have hlen : (StaggerPersistentFrame.frame h off cont rho).length < 1024 := by
    simp [StaggerPersistentFrame.frame]; omega
  have g1 := jumpdest_gasSteps stub192Dest 192 stub192Dest_pc (by norm_num) s _ hlen hrun hcode hfork hnp
  have g2 := pushCont_gasSteps 128 193 stub192Push stub192Push_pc s h off cont rho hstack hrun hcode hfork hnp
  have he : pcAfter (UInt256.ofNat 193) (Control.LoopRaw.pushContTemplate 128) = UInt256.ofNat 195 := by decide
  rw [he] at g2
  have g3 := advJump_gasSteps stub192Jump 195 stub192Jump_pc s
    (UInt256.ofNat 128 :: StaggerPersistentFrame.frame h off cont rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hrun hcode hfork hnp
  have g4 := splitJoin_gasSteps s h off cont (UInt256.ofNat 128) rho hstack hrun hcode hfork hnp
  exact ((g1.trans g2).trans g3).trans g4

/-- The 128 stub: the continuation becomes 64 and the block advance follows directly. -/
def gasSteps_stub128 (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 128, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 133, stack := cont :: StaggerPersistentFrame.frame h off (UInt256.ofNat 64) rho} := by
  have hlen : (StaggerPersistentFrame.frame h off cont rho).length < 1024 := by
    simp [StaggerPersistentFrame.frame]; omega
  have g1 := jumpdest_gasSteps stub128Dest 128 stub128Dest_pc (by norm_num) s _ hlen hrun hcode hfork hnp
  have g2 := setCont_gasSteps 64 129 stub128Set stub128Set_pc (by decide) s h off cont rho hstack hrun hcode hfork hnp
  have he : pcAfter (UInt256.ofNat 129) (Control.LoopRaw.setContTemplate 64) = UInt256.ofNat 133 := by decide
  rw [he] at g2
  exact g1.trans g2

/-- The `MSIZE` at 53 (instruction 32) of the generic last-block test. -/
theorem glMsize_decoded (s : State) (stack : List UInt256)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka) :
    ({s with pc := UInt256.ofNat 227, stack := stack} : State).decodedOp = some .MSIZE := by
  have hd := Control.Artifact.submissionArtifact.decodeAt_op_index 119 .MSIZE
    (by rfl) (by decide) trivial
  apply Control.Artifact.submissionArtifact.state_decodedOp_of ({s with pc := UInt256.ofNat 227, stack := stack} : State) 119
    hcode ?_ .MSIZE none hd (by change Operation.MSIZE.availableInFork s.fork = true; rw [hfork]; rfl)
  change (UInt256.ofNat 227).toNat = Control.Artifact.submissionArtifact.instructionPC 119
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
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hpc : s.pc = glTestSite.startPC)
    (hresult : runInstrSeq glTestCode s = some t) : GasSteps s t := by
  apply DataStepper.runLocatedBlock_sound Control.Artifact.submissionArtifact .Osaka glTestSite.path hcode hfork
  · have hl := PairedHelperBooleanTrace.runLocatedBlock_eq_raw_terminal_sites glTestSite.sites glTestCode
      glTestSite.instruction_eq glTestSite.contiguous s
      (by rw [glTestSite.head_eq]; exact congrArg some hpc.symm) (by
        intro located hmem u v hr
        have hm : located.located.instruction ∈
            glTestSite.sites.dropLast.map (fun item => item.located.instruction) := List.mem_map_of_mem hmem
        rw [List.map_dropLast, glTestSite.instruction_eq] at hm
        simp only [glTestCode, Control.LoopRaw.glTestTemplate, List.dropLast_cons_cons,
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
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 222, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 228, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} := by
  have g1 : GasSteps {s with pc := UInt256.ofNat 222, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat 227, stack := (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} := by
    apply PadLift.gasSteps_of_raw glHeadSite {s with pc := UInt256.ofNat 222, stack := StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp glHead_pc.symm
    · exact PadLift.advancesAll_sound _ (by decide)
    · have hr := Control.LoopRaw.run_glHead s (UInt256.ofNat 222) h off cont rho (by omega) hrun
      have he : pcAfter (UInt256.ofNat 222) Control.LoopRaw.glHeadTemplate = UInt256.ofNat 227 := by decide
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
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 222, stack := StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat Control.LoopRaw.outPC, stack := StaggerPersistentFrame.frame h off cont rho} := by
  have g1 := gasSteps_glHead s h off cont rho hstack hrun hcode hfork hnp
  have g2 : GasSteps {s with pc := UInt256.ofNat 228, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho}
      {s with pc := UInt256.ofNat Control.LoopRaw.outPC, stack := StaggerPersistentFrame.frame h off cont rho} := by
    apply glTest_gasSteps_of_raw {s with pc := UInt256.ofNat 228, stack := UInt256.ofNat (32 * s.activeWords.toNat) ::
        (off + UInt256.ofNat 128) :: StaggerPersistentFrame.frame h off cont rho} _ hcode hfork hrun hnp glTest_pc.symm
    · exact Control.LoopRaw.run_glExit s (UInt256.ofNat 228) _ _ _ _
        (by simp [StaggerPersistentFrame.frame]; omega) hrun hlt (valid_out s hcode)
  exact g1.trans g2

/-- The active size reaches `off + 128`: the generic route jumps to the block advance at 133. -/
def gasSteps_glStay (s : State) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hge : ¬ (UInt256.ofNat (32 * s.activeWords.toNat)).toNat < (off + UInt256.ofNat 128).toNat)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
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
    · have hr := Control.LoopRaw.run_glStay s (UInt256.ofNat 228) (StaggerPersistentFrame.frame h off cont rho) _ _ Control.LoopRaw.outPC
        (by simp [StaggerPersistentFrame.frame]; omega) hrun hge
      have he : pcAfter (UInt256.ofNat 228) (Control.LoopRaw.glTestTemplate Control.LoopRaw.outPC) = UInt256.ofNat 233 := by decide
      rw [he] at hr
      exact hr
  have g3 := pushCont_gasSteps 222 233 glPush glPush_pc s h off cont rho hstack hrun hcode hfork hnp
  have he : pcAfter (UInt256.ofNat 233) (Control.LoopRaw.pushContTemplate 222) = UInt256.ofNat 235 := by decide
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
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.StaggerPersistentLoopSites
