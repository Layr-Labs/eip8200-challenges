import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic
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
    .push ⟨24, by decide⟩ (UInt256.ofNat 475368975196266490007815979009),
    .push ⟨13, by decide⟩ (UInt256.ofNat 1109194275457955143345843994625),
    .push ⟨27, by decide⟩ (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928),
    .push ⟨1, by decide⟩ (UInt256.ofNat 2),
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHL,
    .op (.Dup ⟨1, by decide⟩),
    .op .SUB,
    .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295),
    .push ⟨13, by decide⟩ (UInt256.ofNat 158456325065422163343096938498) ]

private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl

private theorem neutral_hsub (a b : UInt256) : a - b = UInt256.sub a b := rfl

/-- The minus-modulus word is the plus-modulus word less the single lane bit the startup
block shifts into place, so one shifted literal seeds both resident moduli. -/
private theorem modulusMinusFromPlus :
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 36893488147419103233) (UInt256.ofNat 144))
        (UInt256.shiftLeft (UInt256.ofNat 2) (UInt256.ofNat 144)) =
      UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096 := by decide

theorem run_initial (s : State) (pc limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq initialTemplate {s with pc := pc, stack := limit :: rho} =
      some {s with
        pc := pcAfter pc initialTemplate
        stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 0) limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 15) : rho.length + n < 1024 := by omega
  simp [initialTemplate, StaggerPersistentFrame.frame, StackRunBridge.initialHashState,
    Crypto.Ripemd160.H0, Word.ofUInt32, runInstrSeq, DataStepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.exchange, neutral_hadd, neutral_hsub, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    StaggerPersistentBootstrapRaw.factorWord_eq,
    FusedKeyReconstruction.modulusPlus, modulusMinusFromPlus,
    FusedKeyReconstruction.modulusMinus, FusedKeyReconstruction.modulusCombinedPlus, StaggerPersistentBootstrapRaw.fusedMinus_eq,
    StaggerPersistentBootstrapRaw.coefficient30_eq, StaggerPersistentBootstrapRaw.coefficient03_eq,
    StaggerPersistentBootstrapRaw.coefficient02_eq, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl


theorem initial_slice :
    (Artifact.submissionArtifact.instructions.drop 240).take initialTemplate.length = initialTemplate := by rfl

def initialSite : GenericRoundSite Artifact.submissionArtifact .Osaka initialTemplate :=
  StackSiteBuilder.ofSlice initialTemplate 240 initial_slice
    (by change 240 + initialTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := initialTemplate) (by decide)) (by decide)

theorem initial_pc : initialSite.startPC = UInt256.ofNat 362 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 240) = UInt256.ofNat 362
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def jumpCode := PadJump.template 489

theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 3677).take jumpCode.length = jumpCode := by rfl

def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpCode :=
  StackSiteBuilder.ofSlice jumpCode 3677 jump_slice
    (by change 3677 + jumpCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := jumpCode) (by decide)) (by decide)

theorem jump_pc : jumpSite.startPC = UInt256.ofNat 4759 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3677) = UInt256.ofNat 4759
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 489).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 261 = 489 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 261 (by rfl)
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
    GasSteps {s with pc := UInt256.ofNat 362, stack := limit :: rho}
      {s with pc := UInt256.ofNat 481, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 0) limit rho} := by
  apply PadLift.gasSteps_of_raw initialSite {s with pc := UInt256.ofNat 362, stack := limit :: rho} _ hcode hfork hrun hnp initial_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hr := run_initial s (UInt256.ofNat 362) limit rho (by omega) hrun
    have hp : pcAfter (UInt256.ofNat 362) initialTemplate = UInt256.ofNat 481 := by decide
    rw [hp] at hr
    exact hr

/-- After the footer loop the padding code jumps to the block-loop head. -/
def gasSteps_jump (s : State) (frame : List UInt256)
    (hstack : frame.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4759, stack := frame}
      {s with pc := UInt256.ofNat 489, stack := frame} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 4759, stack := frame} _ hcode hfork hrun hnp jump_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template s (UInt256.ofNat 4759) frame 489 (by omega) hrun (valid_loop s hcode)
def partialTemplate : List Instr :=
  [.op .JUMPDEST, .op (.Swap ⟨11, by decide⟩), .push 1 72, .op .ADD,
   .push 1 63, .op .NOT, .op .AND, .op (.Swap ⟨11, by decide⟩)]
theorem partial_slice :
    (Artifact.submissionArtifact.instructions.drop 3638).take partialTemplate.length = partialTemplate := by rfl
def partialSite : GenericRoundSite Artifact.submissionArtifact .Osaka partialTemplate :=
  StackSiteBuilder.ofSlice partialTemplate 3638 partial_slice
    (by change 3638 + partialTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := partialTemplate) (by decide)) (by decide)
theorem partial_pc : partialSite.startPC = UInt256.ofNat 4705 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3638) = UInt256.ofNat 4705
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_partial (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4705, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4715, stack := StaggerPersistentFrame.frame h off (PadLimitArithmetic.rounded limit) rho} := by
  apply PadLift.gasSteps_of_raw partialSite
    {s with pc := UInt256.ofNat 4705, stack := StaggerPersistentFrame.frame h off limit rho} _
    hcode hfork hrun hnp partial_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hcap (n : Nat) (hn : n ≤ 16) : rho.length+n < 1024 := by omega
    simp [partialTemplate, StaggerPersistentFrame.frame, PadLimitArithmetic.rounded,
      runInstrSeq, DataStepper.runInstr, hrun, hcap, List.exchange, Nat.add_assoc,
      Word.word_add_comm]
    exact ⟨rfl, rfl⟩

def guard32Template : List Instr :=
  [.op .CALLDATASIZE, .push ⟨1, by decide⟩ (UInt256.ofNat 32), .op .EQ,
   .push ⟨2, by decide⟩ (UInt256.ofNat 328), .op .JUMPI]
theorem guard32_slice :
    (Artifact.submissionArtifact.instructions.drop 3646).take guard32Template.length = guard32Template := by rfl
def guard32Site : GenericRoundSite Artifact.submissionArtifact .Osaka guard32Template :=
  StackSiteBuilder.ofSlice guard32Template 3646 guard32_slice
    (by change 3646 + guard32Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := guard32Template) (by decide)) (by decide)
theorem guard32_pc : guard32Site.startPC = UInt256.ofNat 4715 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3646) = UInt256.ofNat 4715
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_guard32_miss (s : State) (stack : List UInt256)
    (hstack : stack.length ≤ 1000) (hsize : s.executionEnv.calldata.size < 2^256)
    (hne : s.executionEnv.calldata.size ≠ 32) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4715, stack := stack}
      {s with pc := UInt256.ofNat 4723, stack := stack} := by
  apply PadLift.gasSteps_of_raw guard32Site {s with pc := UInt256.ofNat 4715, stack := stack} _ hcode hfork hrun hnp guard32_pc.symm
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
#print axioms gasSteps_partial
#print axioms gasSteps_guard32_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
