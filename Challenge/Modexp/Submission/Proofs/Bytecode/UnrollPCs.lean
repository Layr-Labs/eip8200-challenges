import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the exponent-bit block

The block is entered by the jump at pc 206, derives `base - 1` at pcs 2372 to 2376,
runs one bit body per iteration from the head at 2377, and leaves through the exit at
pcs 2413 to 2416 back to the byte loop at 210. Certificate names are stable API names,
while their indices and PCs bind the selected artifact.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

open EvmSemantics
open EvmSemantics.EVM

open YulEvmCompiler

@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 139 = 210 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 140 = 213 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 4452 = 5570 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 4453 = 5571 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 4454 = 5573 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 4455 = 5574 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 4484 = 5610 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 4485 = 5611 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 4486 = 5614 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
