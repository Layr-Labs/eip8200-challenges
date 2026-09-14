import Challenge.Ripemd160.Submission.Proofs.Bytecode.FusedKeyReconstruction
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentBootstrapRaw
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate

/-- Entry: the chaining words are pushed in the persistent frame order, then the six
round constants, which stay resident for the whole hash. -/
def initialTemplate : List Instr :=
  [ .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .push ⟨4, by decide⟩ (UInt256.ofNat 1732584193),
    .push ⟨4, by decide⟩ (UInt256.ofNat 271733878),
    .push ⟨4, by decide⟩ (UInt256.ofNat 2562383102),
    .push ⟨4, by decide⟩ (UInt256.ofNat 4023233417),
    .push ⟨4, by decide⟩ (UInt256.ofNat 3285377520),
    .push ⟨13, by decide⟩ (UInt256.ofNat 475368975196266490007815979009),
    .push ⟨13, by decide⟩ (UInt256.ofNat 1109194275457955143345843994625),
    .push ⟨12, by decide⟩ (UInt256.ofNat 36893488147419103231),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHL,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 2),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHL,
    .op .ADD,
    .op (.Swap ⟨0, by decide⟩),
    .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295),
    .push ⟨13, by decide⟩ (UInt256.ofNat 158456325065422163343096938498) ]

private theorem plus_shift : UInt256.shiftLeft (UInt256.ofNat 2) (UInt256.ofNat 144) =
    UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 145) := by decide

private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl

theorem run_initial (s : State) (pc limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq initialTemplate {s with pc := pc, stack := limit :: rho} =
      some {s with
        pc := pcAfter pc initialTemplate
        stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 0) limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 15) : rho.length + n < 1024 := by omega
  simp [initialTemplate, StaggerPersistentFrame.frame, StackRunBridge.initialHashState,
    Crypto.Ripemd160.H0, Word.ofUInt32, runInstrSeq, DataStepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.exchange, neutral_hadd, plus_shift, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    StaggerPersistentBootstrapRaw.factorWord_eq,
    FusedKeyReconstruction.modulusMinus, FusedKeyReconstruction.modulusCombinedPlus, StaggerPersistentBootstrapRaw.fusedMinus_eq,
    StaggerPersistentBootstrapRaw.coefficient30_eq, StaggerPersistentBootstrapRaw.coefficient03_eq,
    StaggerPersistentBootstrapRaw.coefficient02_eq, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl


theorem initial_slice :
    (Artifact.submissionArtifact.instructions.drop 256).take initialTemplate.length = initialTemplate := by rfl

def initialSite : GenericRoundSite Artifact.submissionArtifact .Osaka initialTemplate :=
  StackSiteBuilder.ofSlice initialTemplate 256 initial_slice
    (by change 256 + initialTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := initialTemplate) (by decide)) (by decide)

theorem initial_pc : initialSite.startPC = UInt256.ofNat 381 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 256) = UInt256.ofNat 381
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def jumpCode := PadJump.template 489

theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 3692).take jumpCode.length = jumpCode := by rfl

def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpCode :=
  StackSiteBuilder.ofSlice jumpCode 3692 jump_slice
    (by change 3692 + jumpCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := jumpCode) (by decide)) (by decide)

theorem jump_pc : jumpSite.startPC = UInt256.ofNat 4750 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3692) = UInt256.ofNat 4750
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 489).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 283 = 489 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 283 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 489 = true
  rw [hcode]
  exact h

/-- The chaining words and the six resident round constants are pushed directly after the
calldata copy, above the zero offset and the padded limit. -/
def gasSteps_push (s : State) (limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 381, stack := limit :: rho}
      {s with pc := UInt256.ofNat 478, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 0) limit rho} := by
  apply PadLift.gasSteps_of_raw initialSite {s with pc := UInt256.ofNat 381, stack := limit :: rho} _ hcode hfork hrun hnp initial_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hr := run_initial s (UInt256.ofNat 381) limit rho (by omega) hrun
    have hp : pcAfter (UInt256.ofNat 381) initialTemplate = UInt256.ofNat 478 := by decide
    rw [hp] at hr
    exact hr

/-- After the footer loop the padding code jumps to the block-loop head. -/
def gasSteps_jump (s : State) (frame : List UInt256)
    (hstack : frame.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4750, stack := frame}
      {s with pc := UInt256.ofNat 489, stack := frame} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 4750, stack := frame} _ hcode hfork hrun hnp jump_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template s (UInt256.ofNat 4750) frame 489 (by omega) hrun (valid_loop s hcode)
def fullTemplate : List Instr := [.op .CALLDATASIZE, .op (.Swap ⟨12, by decide⟩), .op .POP]
theorem full_slice :
    (Artifact.submissionArtifact.instructions.drop 280).take fullTemplate.length = fullTemplate := by rfl
def fullSite : GenericRoundSite Artifact.submissionArtifact .Osaka fullTemplate :=
  StackSiteBuilder.ofSlice fullTemplate 280 full_slice
    (by change 280 + fullTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := fullTemplate) (by decide)) (by decide)
theorem full_pc : fullSite.startPC = UInt256.ofNat 486 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 280) = UInt256.ofNat 486
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

/-- The aligned route changes only the full frame's limit after initialization. -/
def gasSteps_full (s : State) (limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 486, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 0) limit rho}
      {s with pc := UInt256.ofNat 489, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 0) (UInt256.ofNat s.executionEnv.calldata.size) rho} := by
  apply PadLift.gasSteps_of_raw fullSite {s with pc := UInt256.ofNat 486, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 0) limit rho} _ hcode hfork hrun hnp full_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hcap (n : Nat) (hn : n ≤ 16) : rho.length+n < 1024 := by omega
    simp [fullTemplate, StaggerPersistentFrame.frame, runInstrSeq, DataStepper.runInstr,
      hrun, hcap, List.exchange, Nat.add_assoc]
    rfl

def partialTemplate : List Instr := [.op .JUMPDEST]
theorem partial_slice :
    (Artifact.submissionArtifact.instructions.drop 3660).take partialTemplate.length = partialTemplate := by rfl
def partialSite : GenericRoundSite Artifact.submissionArtifact .Osaka partialTemplate :=
  StackSiteBuilder.ofSlice partialTemplate 3660 partial_slice
    (by change 3660 + partialTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := partialTemplate) (by decide)) (by decide)
theorem partial_pc : partialSite.startPC = UInt256.ofNat 4705 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3660) = UInt256.ofNat 4705
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_partial (s : State) (stack : List UInt256)
    (hstack : stack.length < 1024) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4705, stack := stack}
      {s with pc := UInt256.ofNat 4706, stack := stack} := by
  apply PadLift.gasSteps_of_raw partialSite {s with pc := UInt256.ofNat 4705, stack := stack} _
    hcode hfork hrun hnp partial_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · simp [partialTemplate, runInstrSeq, DataStepper.runInstr, hrun, hstack]
    rfl

def guard32Template : List Instr :=
  [.op .CALLDATASIZE, .push ⟨1, by decide⟩ (UInt256.ofNat 32), .op .EQ,
   .push ⟨2, by decide⟩ (UInt256.ofNat 328), .op .JUMPI]
theorem guard32_slice :
    (Artifact.submissionArtifact.instructions.drop 3661).take guard32Template.length = guard32Template := by rfl
def guard32Site : GenericRoundSite Artifact.submissionArtifact .Osaka guard32Template :=
  StackSiteBuilder.ofSlice guard32Template 3661 guard32_slice
    (by change 3661 + guard32Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := guard32Template) (by decide)) (by decide)
theorem guard32_pc : guard32Site.startPC = UInt256.ofNat 4706 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3661) = UInt256.ofNat 4706
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_guard32_miss (s : State) (stack : List UInt256)
    (hstack : stack.length ≤ 1000) (hsize : s.executionEnv.calldata.size < 2^256)
    (hne : s.executionEnv.calldata.size ≠ 32) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4706, stack := stack}
      {s with pc := UInt256.ofNat 4714, stack := stack} := by
  apply PadLift.gasSteps_of_raw guard32Site {s with pc := UInt256.ofNat 4706, stack := stack} _ hcode hfork hrun hnp guard32_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hcap (n : Nat) (hn : n ≤ 3) : stack.length+n < 1024 := by omega
    have hcap0 : stack.length < 1024 := by omega
    have hw : (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size := by
      rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsize]
    have heq : UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat s.executionEnv.calldata.size) = UInt256.ofNat 0 := by
      unfold UInt256.eq
      rw [hw, if_neg (by simpa using Ne.symm hne)]
    simp [guard32Template, runInstrSeq, DataStepper.runInstr, hrun, hcap, hcap0, heq,
      UInt256.isTrue, pcAfter, Nat.add_assoc]
    rfl

#print axioms gasSteps_push
#print axioms gasSteps_full
#print axioms gasSteps_guard32_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
