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
  [.push ⟨4, by decide⟩ (UInt256.ofNat 0x67452301),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x10325476),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x98badcfe),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xefcdab89),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xc3d2e1f0),
   .push ⟨14, by decide⟩ (UInt256.ofNat 81129638433496147627271880966145),
   .push ⟨14, by decide⟩ (UInt256.ofNat 162259276866992295254539466964993),
   .push ⟨14, by decide⟩ (UInt256.ofNat 20282409608374036906851256238088),
   .push ⟨14, by decide⟩ (UInt256.ofNat 20282409598929303941081901039615),
   .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295),
   .push ⟨14, by decide⟩ (UInt256.ofNat 20282409608374036907091774406720)]

theorem run_initial (s : State) (pc off limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq initialTemplate {s with pc := pc, stack := off :: limit :: rho} =
      some {s with
        pc := pcAfter pc initialTemplate
        stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 15) : rho.length + n < 1024 := by omega
  simp [initialTemplate, StaggerPersistentFrame.frame, StackRunBridge.initialHashState,
    Crypto.Ripemd160.H0, Word.ofUInt32, runInstrSeq, Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap,
    StaggerPersistentBootstrapRaw.factorWord_eq, StaggerPersistentBootstrapRaw.compactMaskWord_eq,
    StaggerPersistentBootstrapRaw.coefficient30_eq, StaggerPersistentBootstrapRaw.coefficient03_eq,
    StaggerPersistentBootstrapRaw.coefficient02_eq]


theorem initial_slice :
    (Artifact.submissionArtifact.instructions.drop 250).take initialTemplate.length = initialTemplate := by rfl

def initialSite : GenericRoundSite Artifact.submissionArtifact .Osaka initialTemplate :=
  StackSiteBuilder.ofSlice initialTemplate 250 initial_slice
    (by change 250 + initialTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := initialTemplate) (by decide)) (by decide)

theorem initial_pc : initialSite.startPC = UInt256.ofNat 367 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 250) = UInt256.ofNat 367
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def jumpCode := PadJump.template 599

theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 293).take jumpCode.length = jumpCode := by rfl

def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpCode :=
  StackSiteBuilder.ofSlice jumpCode 293 jump_slice
    (by change 293 + jumpCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := jumpCode) (by decide)) (by decide)

theorem jump_pc : jumpSite.startPC = UInt256.ofNat 517 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 293) = UInt256.ofNat 517
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 599).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 344 = 599 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 344 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 599 = true
  rw [hcode]
  exact h

/-- The chaining words and the six resident round constants are pushed directly after the
calldata copy, above the zero offset and the padded limit. -/
def gasSteps_push (s : State) (off limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 367, stack := off :: limit :: rho}
      {s with pc := UInt256.ofNat 472, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState off limit rho} := by
  apply PadLift.gasSteps_of_raw initialSite {s with pc := UInt256.ofNat 367, stack := off :: limit :: rho} _ hcode hfork hrun hnp initial_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · have hr := run_initial s (UInt256.ofNat 367) off limit rho (by omega) hrun
    have hp : pcAfter (UInt256.ofNat 367) initialTemplate = UInt256.ofNat 472 := by decide
    rw [hp] at hr
    exact hr

/-- After the footer loop the padding code jumps to the block-loop head. -/
def gasSteps_jump (s : State) (frame : List UInt256)
    (hstack : frame.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 517, stack := frame}
      {s with pc := UInt256.ofNat 599, stack := frame} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 517, stack := frame} _ hcode hfork hrun hnp jump_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template s (UInt256.ofNat 517) frame 599 (by omega) hrun (valid_loop s hcode)
#print axioms gasSteps_push
#print axioms gasSteps_jump
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
