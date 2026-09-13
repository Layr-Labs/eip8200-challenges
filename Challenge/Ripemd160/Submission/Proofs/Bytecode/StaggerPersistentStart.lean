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
  [ .op .JUMPDEST,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .push ⟨4, by decide⟩ (UInt256.ofNat 1732584193),
    .push ⟨4, by decide⟩ (UInt256.ofNat 271733878),
    .push ⟨4, by decide⟩ (UInt256.ofNat 2562383102),
    .push ⟨4, by decide⟩ (UInt256.ofNat 4023233417),
    .push ⟨4, by decide⟩ (UInt256.ofNat 3285377520),
    .push ⟨13, by decide⟩ (UInt256.ofNat 475368975196266490007815979009),
    .push ⟨13, by decide⟩ (UInt256.ofNat 1109194275457955143345843994625),
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .NOT,
    .push ⟨1, by decide⟩ (UInt256.ofNat 191),
    .op .SHR,
    .push ⟨1, by decide⟩ (UInt256.ofNat 144),
    .op .SHL,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 1),
    .push ⟨1, by decide⟩ (UInt256.ofNat 145),
    .op .SHL,
    .op .ADD,
    .op (.Swap ⟨0, by decide⟩),
    .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295),
    .push ⟨13, by decide⟩ (UInt256.ofNat 158456325065422163343096938498) ]

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
    UInt256.succ, Instr.size, List.exchange, neutral_hadd, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    StaggerPersistentBootstrapRaw.factorWord_eq,
    FusedKeyReconstruction.modulusCombinedMinus, FusedKeyReconstruction.modulusCombinedPlus, StaggerPersistentBootstrapRaw.fusedMinus_eq,
    StaggerPersistentBootstrapRaw.coefficient30_eq, StaggerPersistentBootstrapRaw.coefficient03_eq,
    StaggerPersistentBootstrapRaw.coefficient02_eq, Word.literal_eq_ofNat]
  all_goals repeat first | apply And.intro | rfl


theorem initial_slice :
    (Artifact.submissionArtifact.instructions.drop 262).take initialTemplate.length = initialTemplate := by rfl

def initialSite : GenericRoundSite Artifact.submissionArtifact .Osaka initialTemplate :=
  StackSiteBuilder.ofSlice initialTemplate 262 initial_slice
    (by change 262 + initialTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := initialTemplate) (by decide)) (by decide)

theorem initial_pc : initialSite.startPC = UInt256.ofNat 383 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 262) = UInt256.ofNat 383
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def jumpCode := PadJump.template 383

theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 3725).take jumpCode.length = jumpCode := by rfl

def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpCode :=
  StackSiteBuilder.ofSlice jumpCode 3725 jump_slice
    (by change 3725 + jumpCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := jumpCode) (by decide)) (by decide)

theorem jump_pc : jumpSite.startPC = UInt256.ofNat 4706 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3725) = UInt256.ofNat 4706
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 383).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 262 = 383 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 262 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 383 = true
  rw [hcode]
  exact h

/-- The chaining words and the six resident round constants are pushed directly after the
calldata copy, above the zero offset and the padded limit. -/
def gasSteps_push (s : State) (limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 383, stack := limit :: rho}
      {s with pc := UInt256.ofNat 473, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 0) limit rho} := by
  apply PadLift.gasSteps_of_raw initialSite {s with pc := UInt256.ofNat 383, stack := limit :: rho} _ hcode hfork hrun hnp initial_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hr := run_initial s (UInt256.ofNat 383) limit rho (by omega) hrun
    have hp : pcAfter (UInt256.ofNat 383) initialTemplate = UInt256.ofNat 473 := by decide
    rw [hp] at hr
    exact hr

/-- After the footer loop the padding code jumps to the block-loop head. -/
def gasSteps_jump (s : State) (frame : List UInt256)
    (hstack : frame.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4706, stack := frame}
      {s with pc := UInt256.ofNat 383, stack := frame} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 4706, stack := frame} _ hcode hfork hrun hnp jump_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template s (UInt256.ofNat 4706) frame 383 (by omega) hrun (valid_loop s hcode)
def fullTemplate : List Instr := [.op .POP, .op .CALLDATASIZE]
theorem full_slice :
    (Artifact.submissionArtifact.instructions.drop 260).take fullTemplate.length = fullTemplate := by rfl
def fullSite : GenericRoundSite Artifact.submissionArtifact .Osaka fullTemplate :=
  StackSiteBuilder.ofSlice fullTemplate 260 full_slice
    (by change 260 + fullTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := fullTemplate) (by decide)) (by decide)
theorem full_pc : fullSite.startPC = UInt256.ofNat 381 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 260) = UInt256.ofNat 381
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_full (s : State) (limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 381, stack := limit :: rho}
      {s with pc := UInt256.ofNat 383, stack := UInt256.ofNat s.executionEnv.calldata.size :: rho} := by
  apply PadLift.gasSteps_of_raw fullSite {s with pc := UInt256.ofNat 381, stack := limit :: rho} _
    hcode hfork hrun hnp full_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hc : rho.length + 1 < 1024 := by omega
    have hc0 : rho.length < 1024 := by omega
    simp [fullTemplate, runInstrSeq, DataStepper.runInstr, hrun, hc, hc0]
    rfl

def partialTemplate : List Instr := [.op .JUMPDEST]
theorem partial_slice :
    (Artifact.submissionArtifact.instructions.drop 3698).take partialTemplate.length = partialTemplate := by rfl
def partialSite : GenericRoundSite Artifact.submissionArtifact .Osaka partialTemplate :=
  StackSiteBuilder.ofSlice partialTemplate 3698 partial_slice
    (by change 3698 + partialTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := partialTemplate) (by decide)) (by decide)
theorem partial_pc : partialSite.startPC = UInt256.ofNat 4669 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3698) = UInt256.ofNat 4669
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_partial (s : State) (stack : List UInt256)
    (hstack : stack.length < 1024) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4669, stack := stack}
      {s with pc := UInt256.ofNat 4670, stack := stack} := by
  apply PadLift.gasSteps_of_raw partialSite {s with pc := UInt256.ofNat 4669, stack := stack} _
    hcode hfork hrun hnp partial_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · simp [partialTemplate, runInstrSeq, DataStepper.runInstr, hrun, hstack]
    rfl

#print axioms gasSteps_push
#print axioms gasSteps_jump
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
