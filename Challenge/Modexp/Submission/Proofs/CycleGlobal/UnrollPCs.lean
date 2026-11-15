import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the exponent-bit block

The block is entered by the jump at pc 206, derives `base - 1` at pcs 2604 to 2608,
runs one bit body per iteration from the head at 2609, and leaves through the exit at
pcs 2645 to 2648 back to the byte loop at 210. Certificate names are stable API names,
while their indices and PCs bind the selected artifact.
-/
namespace CycleSubmission.Global.UnrollPCs
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
@[simp] theorem pc485 : CycleSubmission.Artifact.artifact.instructionPC 129 = 168 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc486 : CycleSubmission.Artifact.artifact.instructionPC 130 = 171 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2414 : CycleSubmission.Artifact.artifact.instructionPC 8085 = 10705 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2415 : CycleSubmission.Artifact.artifact.instructionPC 8086 = 10706 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2416 : CycleSubmission.Artifact.artifact.instructionPC 8087 = 10708 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2417 : CycleSubmission.Artifact.artifact.instructionPC 8088 = 10709 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2554 : CycleSubmission.Artifact.artifact.instructionPC 8117 = 10745 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2555 : CycleSubmission.Artifact.artifact.instructionPC 8118 = 10746 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
@[simp] theorem pc2556 : CycleSubmission.Artifact.artifact.instructionPC 8119 = 10749 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl
end CycleSubmission.Global.UnrollPCs
