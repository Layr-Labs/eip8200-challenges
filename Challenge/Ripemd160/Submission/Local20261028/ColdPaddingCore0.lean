import Challenge.Ripemd160.Submission.Local20261028.ColdShared32Scratch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Local20261028.ColdTrace
import Challenge.Ripemd160.Submission.Local20261028.ColdMain
import Challenge.Ripemd160.Submission.Local20261028.ColdStaggerPersistentStart
import Challenge.Ripemd160.Submission.Local20261028.ColdGuardFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-!
# Direct execution of the RIPEMD-160 padding function (setup, guard, sentinel, footer loop and exit)

The fixed setup and the eight-iteration little-endian footer loop are exposed
as located paths.  The resulting state is shared by correctness and exact gas
accounting.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.PaddingTrace
open EvmSemantics EvmSemantics.EVM
@[simp] theorem inherited_valid_pad :
    EvmSemantics.EVM.Decode.isValidJumpDest submissionBytecode 143 = true := by
  have hp : Control.Artifact.submissionArtifact.instructionPC 81 = 143 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have h := Control.Artifact.submissionArtifact.isValidJumpDest_index 81 (by rfl)
  rw [hp] at h
  exact h

@[simp] theorem inherited_pc_97 : Control.Artifact.submissionArtifact.instructionPC 105 = 209 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_128 : Control.Artifact.submissionArtifact.instructionPC 136 = 309 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_129 : Control.Artifact.submissionArtifact.instructionPC 137 = 310 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_130 : Control.Artifact.submissionArtifact.instructionPC 138 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_131 : Control.Artifact.submissionArtifact.instructionPC 139 = 314 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_132 : Control.Artifact.submissionArtifact.instructionPC 140 = 315 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_133 : Control.Artifact.submissionArtifact.instructionPC 141 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_145 : Control.Artifact.submissionArtifact.instructionPC 153 = 447 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_146 : Control.Artifact.submissionArtifact.instructionPC 154 = 456 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_147 : Control.Artifact.submissionArtifact.instructionPC 155 = 457 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_148 : Control.Artifact.submissionArtifact.instructionPC 156 = 458 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_149 : Control.Artifact.submissionArtifact.instructionPC 157 = 460 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_3368 : Control.Artifact.submissionArtifact.instructionPC 3350 = 4583 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_3369 : Control.Artifact.submissionArtifact.instructionPC 3351 = 4584 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_3370 : Control.Artifact.submissionArtifact.instructionPC 3352 = 4585 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_3371 : Control.Artifact.submissionArtifact.instructionPC 3353 = 4586 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_3372 : Control.Artifact.submissionArtifact.instructionPC 3354 = 4587 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_3373 : Control.Artifact.submissionArtifact.instructionPC 3355 = 4589 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_3374 : Control.Artifact.submissionArtifact.instructionPC 3356 = 4590 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_3375 : Control.Artifact.submissionArtifact.instructionPC 3357 = 4591 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_5411 : Control.Artifact.submissionArtifact.instructionPC 6810 = 9998 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_5412 : Control.Artifact.submissionArtifact.instructionPC 6811 = 10000 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_5413 : Control.Artifact.submissionArtifact.instructionPC 6812 = 10001 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_5414 : Control.Artifact.submissionArtifact.instructionPC 6813 = 10002 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem inherited_pc_5415 : Control.Artifact.submissionArtifact.instructionPC 6814 = 10003 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl


open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem literalZeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Challenge.EvmProof.PcEncoding.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.DataStepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.PaddingTrace
