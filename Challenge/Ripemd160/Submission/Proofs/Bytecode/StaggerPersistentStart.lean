import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate

def initialTemplate : List Instr :=
  [.push ⟨4, by decide⟩ (UInt256.ofNat 0xc3d2e1f0),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x10325476),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x98badcfe),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0xefcdab89),
   .push ⟨4, by decide⟩ (UInt256.ofNat 0x67452301)]

theorem run_initial (s : State) (pc off limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1014) (hrun : s.halt = .Running) :
    runInstrSeq initialTemplate {s with pc := pc, stack := off :: limit :: rho} =
      some {s with
        pc := pcAfter pc initialTemplate
        stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState off limit rho} := by
  have hcap (n : Nat) (hn : n ≤ 9) : rho.length + n < 1024 := by omega
  simp [initialTemplate, StaggerPersistentFrame.frame, StackRunBridge.initialHashState,
    Crypto.Ripemd160.H0, Word.ofUInt32, runInstrSeq, Stepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.getElem?_cons_zero, Nat.add_assoc, hrun, hcap]


theorem initial_slice :
    (Artifact.submissionArtifact.instructions.drop 219).take initialTemplate.length = initialTemplate := by rfl

def initialSite : GenericRoundSite Artifact.submissionArtifact .Osaka initialTemplate :=
  StackSiteBuilder.ofSlice initialTemplate 219 initial_slice
    (by change 219 + initialTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := initialTemplate) (by decide)) (by decide)

theorem initial_pc : initialSite.startPC = UInt256.ofNat 331 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 219) = UInt256.ofNat 331
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def jumpCode := PadJump.template 484

theorem jump_slice :
    (Artifact.submissionArtifact.instructions.drop 224).take jumpCode.length = jumpCode := by rfl

def jumpSite : GenericRoundSite Artifact.submissionArtifact .Osaka jumpCode :=
  StackSiteBuilder.ofSlice jumpCode 224 jump_slice
    (by change 224 + jumpCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := jumpCode) (by decide)) (by decide)

theorem jump_pc : jumpSite.startPC = UInt256.ofNat 356 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 224) = UInt256.ofNat 356
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 484).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 296 = 484 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 296 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 484 = true
  rw [hcode]
  exact h

def gasSteps (s : State) (off limit : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 331, stack := off :: limit :: rho}
      {s with pc := UInt256.ofNat 484, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState off limit rho} := by
  have gi : GasSteps {s with pc := UInt256.ofNat 331, stack := off :: limit :: rho}
      {s with pc := UInt256.ofNat 356, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState off limit rho} := by
    apply PadLift.gasSteps_of_raw initialSite {s with pc := UInt256.ofNat 331, stack := off :: limit :: rho} _ hcode hfork hrun hnp initial_pc.symm
    · apply PadLift.advancesAll_sound; decide
    · have hr := run_initial s (UInt256.ofNat 331) off limit rho (by omega) hrun
      have hp : pcAfter (UInt256.ofNat 331) initialTemplate = UInt256.ofNat 356 := by decide
      rw [hp] at hr
      exact hr
  have gj : GasSteps {s with pc := UInt256.ofNat 356, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState off limit rho}
      {s with pc := UInt256.ofNat 484, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState off limit rho} := by
    apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 356, stack := StaggerPersistentFrame.frame StackRunBridge.initialHashState off limit rho} _ hcode hfork hrun hnp jump_pc.symm
    · apply PadLift.advancesAll_sound; decide
    · exact PadJump.run_template s (UInt256.ofNat 356)
        (StaggerPersistentFrame.frame StackRunBridge.initialHashState off limit rho) 484
        (by simp [StaggerPersistentFrame.frame]; omega) hrun (valid_loop s hcode)
  exact gi.trans gj
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
