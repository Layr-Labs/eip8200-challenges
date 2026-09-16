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
    .push ⟨4, by decide⟩ (UInt256.ofNat 1732584221),
    .push ⟨4, by decide⟩ (UInt256.ofNat 4023233445),
    .push ⟨4, by decide⟩ (UInt256.ofNat 2562383130),
    .push ⟨4, by decide⟩ (UInt256.ofNat 271733906),
    .push ⟨4, by decide⟩ (UInt256.ofNat 3285377548),
    .push ⟨13, by decide⟩ (UInt256.ofNat 475368975196266490007815979037),
    .push ⟨13, by decide⟩ (UInt256.ofNat 1109194275457955143345843994653),
    .push ⟨9, by decide⟩ (UInt256.ofNat 36893488147419103261),
    .push ⟨1, by decide⟩ (UInt256.ofNat 172),
    .op .SHL,
    .push ⟨9, by decide⟩ (UInt256.ofNat 36893488147419103259),
    .push ⟨1, by decide⟩ (UInt256.ofNat 172),
    .op .SHL,
    .push ⟨4, by decide⟩ (UInt256.ofNat 4294967323),
    .push ⟨13, by decide⟩ (UInt256.ofNat 158456325065422163343096938526) ]

private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl

private theorem neutral_hsub (a b : UInt256) : a - b = UInt256.sub a b := rfl

/-- The minus-modulus word is the plus-modulus word less the single lane bit the startup
block shifts into place, so one shifted literal seeds both resident moduli. -/
private theorem modulusMinusFromPlus :
    UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 36893488147419103261) (UInt256.ofNat 172))
        (UInt256.shiftLeft (UInt256.ofNat 2) (UInt256.ofNat 172)) =
      UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324124 := by decide

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
    (Artifact.submissionArtifact.instructions.drop 234).take initialTemplate.length = initialTemplate := by rfl

def initialSite : GenericRoundSite Artifact.submissionArtifact .Osaka initialTemplate :=
  StackSiteBuilder.ofSlice initialTemplate 237 initial_slice
    (by change 237 + initialTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := initialTemplate) (by decide)) (by decide)

theorem initial_pc : initialSite.startPC = UInt256.ofNat 386 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 234) = UInt256.ofNat 386
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def jumpCode := PadJump.template 465

theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 3647).take jumpCode.length = jumpCode := by rfl

def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpCode :=
  StackSiteBuilder.ofSlice jumpCode 3650 jump_slice
    (by change 3650 + jumpCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := jumpCode) (by decide)) (by decide)

theorem jump_pc : jumpSite.startPC = UInt256.ofNat 4791 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3647) = UInt256.ofNat 4791
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 493).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 252 = 493 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 258 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 465 = true
  rw [hcode]
  exact h

/-- The chaining words and the six resident round constants are pushed directly after the
calldata copy, above the zero offset and the padded limit. -/
def gasSteps_push (s : State) (limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 386, stack := limit :: rho}
      {s with pc := UInt256.ofNat 485, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 0) limit rho} := by
  apply PadLift.gasSteps_of_raw initialSite {s with pc := UInt256.ofNat 386, stack := limit :: rho} _ hcode hfork hrun hnp initial_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hr := run_initial s (UInt256.ofNat 386) limit rho (by omega) hrun
    have hp : pcAfter (UInt256.ofNat 386) initialTemplate = UInt256.ofNat 485 := by decide
    rw [hp] at hr
    exact hr

/-- After the footer loop the padding code jumps to the block-loop head. -/
def gasSteps_jump (s : State) (frame : List UInt256)
    (hstack : frame.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4791, stack := frame}
      {s with pc := UInt256.ofNat 493, stack := frame} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 4791, stack := frame} _ hcode hfork hrun hnp jump_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template s (UInt256.ofNat 4791) frame 465 (by omega) hrun (valid_loop s hcode)
def roundTemplate : List Instr :=
  [.op (.Swap ⟨11, by decide⟩), .push 1 72, .op .ADD,
   .push 1 63, .op .NOT, .op .AND, .op (.Swap ⟨11, by decide⟩)]
theorem round_slice :
    (Artifact.submissionArtifact.instructions.drop 3614).take roundTemplate.length = roundTemplate := by rfl
def roundSite : GenericRoundSite Artifact.submissionArtifact .Osaka roundTemplate :=
  StackSiteBuilder.ofSlice roundTemplate 3617 round_slice
    (by change 3617 + roundTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := roundTemplate) (by decide)) (by decide)
theorem round_pc : roundSite.startPC = UInt256.ofNat 4746 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3614) = UInt256.ofNat 4746
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_round (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4746, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4755, stack := StaggerPersistentFrame.frame h off (PadLimitArithmetic.rounded limit) rho} := by
  apply PadLift.gasSteps_of_raw roundSite
    {s with pc := UInt256.ofNat 4746, stack := StaggerPersistentFrame.frame h off limit rho} _
    hcode hfork hrun hnp round_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hcap (n : Nat) (hn : n ≤ 16) : rho.length+n < 1024 := by omega
    simp [roundTemplate, StaggerPersistentFrame.frame, PadLimitArithmetic.rounded,
      runInstrSeq, DataStepper.runInstr, hrun, hcap, List.exchange, Nat.add_assoc,
      Word.word_add_comm]
    exact ⟨rfl, rfl⟩

def guard32Template : List Instr :=
  [ .op .CALLDATASIZE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .EQ,
    .push ⟨2, by decide⟩ (UInt256.ofNat 350),
    .op .JUMPI ]
theorem guard32_slice :
    (Artifact.submissionArtifact.instructions.drop 3609).take guard32Template.length = guard32Template := by rfl
def guard32Site : GenericRoundSite Artifact.submissionArtifact .Osaka guard32Template :=
  StackSiteBuilder.ofSlice guard32Template 3612 guard32_slice
    (by change 3612 + guard32Template.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := guard32Template) (by decide)) (by decide)
theorem guard32_pc : guard32Site.startPC = UInt256.ofNat 4738 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3609) = UInt256.ofNat 4738
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_guard32_miss (s : State) (stack : List UInt256)
    (hstack : stack.length ≤ 1000) (hsize : s.executionEnv.calldata.size < 2^256)
    (hne : s.executionEnv.calldata.size ≠ 32) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4738, stack := stack}
      {s with pc := UInt256.ofNat 4746, stack := stack} := by
  apply PadLift.gasSteps_of_raw guard32Site {s with pc := UInt256.ofNat 4738, stack := stack} _ hcode hfork hrun hnp guard32_pc.symm
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

def entryTemplate : List Instr := [.op .JUMPDEST]
theorem entry_slice :
    (Artifact.submissionArtifact.instructions.drop 3608).take entryTemplate.length = entryTemplate := by rfl
def entrySite : GenericRoundSite Artifact.submissionArtifact .Osaka entryTemplate :=
  StackSiteBuilder.ofSlice entryTemplate 3611 entry_slice
    (by change 3611 + entryTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := entryTemplate) (by decide)) (by decide)
theorem entry_pc : entrySite.startPC = UInt256.ofNat 4737 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3608) = UInt256.ofNat 4737
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_entry (s : State) (stack : List UInt256) (hstack : stack.length ≤ 1000)
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4737, stack := stack}
      {s with pc := UInt256.ofNat 4738, stack := stack} := by
  apply PadLift.gasSteps_of_raw entrySite {s with pc := UInt256.ofNat 4737, stack := stack} _ hcode hfork hrun hnp entry_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · simpa only [entryTemplate, show UInt256.ofNat 4737 + UInt256.ofNat 1 = UInt256.ofNat 4738 by decide] using
      PadJump.run_merge s (UInt256.ofNat 4737) stack (by omega) hrun

def gasSteps_partial (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hsize : s.executionEnv.calldata.size < 2^256)
    (hne : s.executionEnv.calldata.size ≠ 32) :
    GasSteps {s with pc := UInt256.ofNat 4737, stack := StaggerPersistentFrame.frame h off limit rho}
      {s with pc := UInt256.ofNat 4755, stack := StaggerPersistentFrame.frame h off (PadLimitArithmetic.rounded limit) rho} := by
  let F := StaggerPersistentFrame.frame h off limit rho
  have hF : F.length ≤ 1000 := by
    simp only [F, StaggerPersistentFrame.frame, List.length_append, List.length_cons, List.length_nil]
    omega
  have ge := gasSteps_entry s F hF hrun hcode hfork hnp
  have gg := gasSteps_guard32_miss s F hF hsize hne hrun hcode hfork hnp
  have gr := gasSteps_round s h off limit rho hstack hrun hcode hfork hnp
  exact ge.trans (gg.trans gr)

#print axioms gasSteps_push
#print axioms gasSteps_round
#print axioms gasSteps_entry
#print axioms gasSteps_partial
#print axioms gasSteps_guard32_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
