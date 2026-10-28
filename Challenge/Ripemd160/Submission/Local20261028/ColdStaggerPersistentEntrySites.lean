import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDivMaskCache
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntryRaw
import Challenge.Ripemd160.Submission.Local20261028.ColdCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Local20261028.ColdLoopRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.StaggerPersistentEntrySites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentEntryRaw StaggerPersistentFrame PairedMask32Cache
/-! The block-advance code at 133..142 (`POP SWAP11 PUSH1 0x40 ADD SWAP11 PUSH2 0x1cd JUMP`):
the increment lives in Control.StaggerPersistentLoopSites, the swap back and the jump to the loop head
are here. -/

def jumpCode : List Instr := PadJump.template 461
theorem jump_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 79).take jumpCode.length = jumpCode := by rfl
def jumpSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka jumpCode :=
  StackSiteBuilder.ofSlice jumpCode 79 jump_slice
    (by change 79 + jumpCode.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check jumpCode (by decide)) (by decide)
theorem jump_pc : jumpSite.startPC = UInt256.ofNat 139 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 79) = UInt256.ofNat 139
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def swapCode : List Instr := Control.LoopRaw.backTemplate

theorem swap_slice :
    (Control.Artifact.submissionArtifact.instructions.drop 78).take swapCode.length = swapCode := by rfl

def swapSite : GenericRoundSite Control.Artifact.submissionArtifact .Osaka swapCode :=
  StackSiteBuilder.ofSlice swapCode 78 swap_slice
    (by change 78 + swapCode.length ≤ Control.Artifact.submissionInstructions.length
        rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check swapCode (by decide)) (by decide)

theorem swap_pc : swapSite.startPC = UInt256.ofNat 138 := by
  change UInt256.ofNat (Control.Artifact.submissionArtifact.instructionPC 78) = UInt256.ofNat 138
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

theorem valid_finish (s : State) (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 8397).toNat = true := by
  have hpc : Control.Artifact.submissionArtifact.instructionPC 6218 = 8397 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Control.Artifact.submissionArtifact.isValidJumpDest_index 6218 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 8397 = true
  rw [hcode]
  exact h

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 461).toNat = true := by
  have hpc : Control.Artifact.submissionArtifact.instructionPC 158 = 461 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Control.Artifact.submissionArtifact.isValidJumpDest_index 158 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 461 = true
  rw [hcode]
  exact h

theorem valid_gl (s : State) (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 222).toNat = true := by
  have hpc : Control.Artifact.submissionArtifact.instructionPC 115 = 222 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Control.Artifact.submissionArtifact.isValidJumpDest_index 115 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 222 = true
  rw [hcode]
  exact h

theorem valid_pad (s : State) (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 64).toNat = true := by
  have hpc : Control.Artifact.submissionArtifact.instructionPC 34 = 64 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Control.Artifact.submissionArtifact.isValidJumpDest_index 34 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 64 = true
  rw [hcode]
  exact h

theorem valid_stub128 (s : State) (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 128).toNat = true := by
  have hpc : Control.Artifact.submissionArtifact.instructionPC 71 = 128 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Control.Artifact.submissionArtifact.isValidJumpDest_index 71 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 128 = true
  rw [hcode]
  exact h

theorem valid_adv (s : State) (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 210).toNat = true := by
  have hpc : Control.Artifact.submissionArtifact.instructionPC 106 = 210 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Control.Artifact.submissionArtifact.isValidJumpDest_index 106 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 210 = true
  rw [hcode]
  exact h

theorem valid_stub192 (s : State) (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 192).toNat = true := by
  have hpc : Control.Artifact.submissionArtifact.instructionPC 93 = 192 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Control.Artifact.submissionArtifact.isValidJumpDest_index 93 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 192 = true
  rw [hcode]
  exact h

/-- The advanced offset goes back into slot 11. -/
def gasSteps_swapBack (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 138, stack := exitFrame h off limit rho}
      {s with pc := UInt256.ofNat 139, stack := frame h off limit rho} := by
  apply PadLift.gasSteps_of_raw swapSite {s with pc := UInt256.ofNat 138, stack := exitFrame h off limit rho} _ hcode hfork hrun hnp swap_pc.symm
  · exact PadLift.advancesAll_sound _ (by decide)
  · have hr := Control.LoopRaw.run_back s (UInt256.ofNat 138) h off limit rho (by omega) hrun
    have he : pcAfter (UInt256.ofNat 138) Control.LoopRaw.backTemplate = UInt256.ofNat 139 := by decide
    rw [he] at hr
    exact hr

/-- Jump back to the loop head. -/
def gasSteps_back (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 139, stack := rho}
      {s with pc := UInt256.ofNat 461, stack := rho} := by
  apply PadLift.gasSteps_of_raw jumpSite {s with pc := UInt256.ofNat 139, stack := rho} _ hcode hfork hrun hnp jump_pc.symm
  · apply PadLift.advancesAll_sound; decide
  · exact PadJump.run_template s (UInt256.ofNat 139) rho 461 (by omega) hrun (valid_loop s hcode)

#print axioms gasSteps_back
#print axioms gasSteps_swapBack
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.StaggerPersistentEntrySites
