import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDivMaskCache
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntryRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadJump
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate StaggerPersistentEntryRaw StaggerPersistentFrame PairedMask32Cache
/-! Valid jump destinations of the loop: the block exit's targets 48, 64, 128, 192, the output
entry 4733, the loop head 461, and the appended continuations `Z` (5100) and `T` (5105). -/

theorem valid_finish (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 4733).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3484 = 4733 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3484 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 4733 = true
  rw [hcode]
  exact h

theorem valid_loop (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 461).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 179 = 461 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 179 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 461 = true
  rw [hcode]
  exact h

theorem valid_gl (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 48).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 29 = 48 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 29 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 48 = true
  rw [hcode]
  exact h

theorem valid_pad (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 64).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 40 = 64 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 40 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 64 = true
  rw [hcode]
  exact h

theorem valid_stub128 (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 128).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 71 = 128 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 71 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 128 = true
  rw [hcode]
  exact h

theorem valid_stub192 (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 192).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 112 = 192 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 112 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 192 = true
  rw [hcode]
  exact h

theorem valid_cont192 (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 5100).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3750 = 5100 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3750 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 5100 = true
  rw [hcode]
  exact h

theorem valid_advance (s : State) (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 5105).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3754 = 5105 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3754 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 5105 = true
  rw [hcode]
  exact h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentEntrySites
