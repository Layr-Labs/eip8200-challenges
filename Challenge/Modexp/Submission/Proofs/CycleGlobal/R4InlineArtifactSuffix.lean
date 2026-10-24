import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.R4InlinePCBasis
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option maxRecDepth 60000
set_option maxHeartbeats 8000000
noncomputable section
set_option warningAsError true
namespace CycleSubmission.Global.Fast.R4InlineArtifactSuffix
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
def instructions : List Instr := CycleSubmission.Artifact.instructions.drop 3130
theorem instructions_eq : CycleSubmission.Artifact.artifact.instructions.drop 3130 = instructions := by rfl

theorem startPC : CycleSubmission.Artifact.artifact.instructionPC 3130 = 4037 := by
  rw [PCFast.instructionPC_eq_byteLength]
  rfl

theorem pc (offset result : Nat)
    (h : 4037 + PCFast.byteLength (instructions.take offset) = result) :
    CycleSubmission.Artifact.artifact.instructionPC (3130 + offset) = result := by
  exact (R4InlinePCBasis.instructionPC_add CycleSubmission.Artifact.artifact 3130 offset).trans
    ((congrArg₂ Nat.add startPC
      (congrArg (fun xs : List Instr => PCFast.byteLength (xs.take offset)) instructions_eq)).trans h)

theorem slice (offset count : Nat) (target : List Instr)
    (h : (instructions.drop offset).take count = target) :
    (CycleSubmission.Artifact.artifact.instructions.drop (3130 + offset)).take count = target := by
  exact (congrArg (fun xs : List Instr => xs.take count)
    (List.drop_drop (i := offset) (j := 3130) (l := CycleSubmission.Artifact.artifact.instructions)).symm).trans
    ((congrArg (fun xs : List Instr => (xs.drop offset).take count) instructions_eq).trans h)
end CycleSubmission.Global.Fast.R4InlineArtifactSuffix
