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
  [.op .JUMPDEST, .push ⟨0, by decide⟩ ⟨0⟩, .push ⟨4, by decide⟩ (UInt256.ofNat 0x67452301),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x10325476),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x98badcfe),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xefcdab89),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xc3d2e1f0),
   .push ⟨14, by decide⟩ (UInt256.ofNat 81129638433496147627271880966145),
   .push ⟨14, by decide⟩ (UInt256.ofNat 162259276866992295254539466964993),
   .push ⟨14, by decide⟩ (UInt256.ofNat 20282409608374036906851256238088),
   .push ⟨16, by decide⟩ (UInt256.ofNat 20282409598929303941081901039615),
   .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295),
   .push ⟨14, by decide⟩ (UInt256.ofNat 20282409608374036907091774406720)]

theorem run_initial (s : State) (pc limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq initialTemplate {s with pc := pc, stack := limit :: rho} =
      some {s with
        pc := pcAfter pc initialTemplate
        stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 0) limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 15) : rho.length + n < 1024 := by omega
  simp [initialTemplate, StaggerPersistentFrame.frame, StackRunBridge.initialHashState,
    Crypto.Ripemd160.H0, Word.ofUInt32, runInstrSeq, DataStepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    StaggerPersistentBootstrapRaw.factorWord_eq, StaggerPersistentBootstrapRaw.compactMaskWord_eq,
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

theorem initial_pc : initialSite.startPC = UInt256.ofNat 376 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 256) = UInt256.ofNat 376
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def jumpCode := PadJump.template 376

theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 3786).take jumpCode.length = jumpCode := by rfl

def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpCode :=
  StackSiteBuilder.ofSlice jumpCode 3786 jump_slice
    (by change 3786 + jumpCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := jumpCode) (by decide)) (by decide)

theorem jump_pc : jumpSite.startPC = UInt256.ofNat 4775 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3786) = UInt256.ofNat 4775
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 376).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 256 = 376 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 256 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 376 = true
  rw [hcode]
  exact h

/-- The chaining words and the six resident round constants are pushed directly after the
calldata copy, above the zero offset and the padded limit. -/
def gasSteps_push (s : State) (limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 376, stack := limit :: rho}
      {s with pc := UInt256.ofNat 485, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 0) limit rho} := by
  apply PadLift.gasSteps_of_raw initialSite {s with pc := UInt256.ofNat 376, stack := limit :: rho} _ hcode hfork hrun hnp initial_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hr := run_initial s (UInt256.ofNat 376) limit rho (by omega) hrun
    have hp : pcAfter (UInt256.ofNat 376) initialTemplate = UInt256.ofNat 485 := by decide
    rw [hp] at hr
    exact hr

/-- After the footer loop the padding code jumps to the block-loop head. -/
def gasSteps_jump (s : State) (frame : List UInt256)
    (hstack : frame.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4775, stack := frame}
      {s with pc := UInt256.ofNat 376, stack := frame} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 4775, stack := frame} _ hcode hfork hrun hnp jump_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template s (UInt256.ofNat 4775) frame 376 (by omega) hrun (valid_loop s hcode)
def fullTemplate : List Instr := [.op .POP, .op .CALLDATASIZE]
theorem full_slice :
    (Artifact.submissionArtifact.instructions.drop 254).take fullTemplate.length = fullTemplate := by rfl
def fullSite : GenericRoundSite Artifact.submissionArtifact .Osaka fullTemplate :=
  StackSiteBuilder.ofSlice fullTemplate 254 full_slice
    (by change 254 + fullTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := fullTemplate) (by decide)) (by decide)
theorem full_pc : fullSite.startPC = UInt256.ofNat 374 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 254) = UInt256.ofNat 374
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_full (s : State) (limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 374, stack := limit :: rho}
      {s with pc := UInt256.ofNat 376, stack := UInt256.ofNat s.executionEnv.calldata.size :: rho} := by
  apply PadLift.gasSteps_of_raw fullSite {s with pc := UInt256.ofNat 374, stack := limit :: rho} _
    hcode hfork hrun hnp full_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hc : rho.length + 1 < 1024 := by omega
    have hc0 : rho.length < 1024 := by omega
    simp [fullTemplate, runInstrSeq, DataStepper.runInstr, hrun, hc, hc0]
    rfl

def partialTemplate : List Instr := [.op .JUMPDEST]
theorem partial_slice :
    (Artifact.submissionArtifact.instructions.drop 3759).take partialTemplate.length = partialTemplate := by rfl
def partialSite : GenericRoundSite Artifact.submissionArtifact .Osaka partialTemplate :=
  StackSiteBuilder.ofSlice partialTemplate 3759 partial_slice
    (by change 3759 + partialTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := partialTemplate) (by decide)) (by decide)
theorem partial_pc : partialSite.startPC = UInt256.ofNat 4738 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3759) = UInt256.ofNat 4738
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_partial (s : State) (stack : List UInt256)
    (hstack : stack.length < 1024) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4738, stack := stack}
      {s with pc := UInt256.ofNat 4739, stack := stack} := by
  apply PadLift.gasSteps_of_raw partialSite {s with pc := UInt256.ofNat 4738, stack := stack} _
    hcode hfork hrun hnp partial_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · simp [partialTemplate, runInstrSeq, DataStepper.runInstr, hrun, hstack]
    rfl

#print axioms gasSteps_push
#print axioms gasSteps_jump
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
