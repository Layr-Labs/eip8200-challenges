import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Global.PrefixPC
open YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode

def width : Instr → Nat
  | .op _ => 1
  | .push w _ => 1 + w.val

theorem length_eq (xs : List Instr) : PCFast.byteLength xs = (xs.map width).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [PCFast.byteLength, width, ih]

theorem pc_add (a : ProgramArtifact) (base count : Nat) :
    a.instructionPC (base+count) = a.instructionPC base + PCFast.byteLength ((a.instructions.drop base).take count) := by
  simp only [PCFast.instructionPC_eq_byteLength, List.take_add]
  simp only [length_eq, List.map_append, List.sum_append]

private theorem widths_eq :
    (((CycleSubmission.Artifact.instructions.drop 370).take (2533-370)).map width) =
    (((Artifact.submissionInstructions.drop 370).take (2533-370)).map width) := by rfl

/-- Instruction addresses in the unchanged dispatch/conversion prefix agree
with the accepted proof base, despite changed destination literals. -/
@[simp] theorem eq_old (i : Nat) (hlo : 370 ≤ i) (hhi : i ≤ 2533) :
    CycleSubmission.Artifact.artifact.instructionPC i = Artifact.submissionArtifact.instructionPC i := by
  have h : (((CycleSubmission.Artifact.instructions.drop 370).take (i-370)).map width) =
      (((Artifact.submissionInstructions.drop 370).take (i-370)).map width) := by
    have h := congrArg (List.take (i-370)) widths_eq
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-370 ≤ 2533-370 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 370 = 533 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 370 = 533 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 370+(i-370)=i := by omega
  rw [← hi, pc_add, pc_add, ha, hb]
  change 533 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 370).take (i-370)) =
    533 + PCFast.byteLength ((Artifact.submissionInstructions.drop 370).take (i-370))
  rw [length_eq, length_eq, h]

end CycleSubmission.Global.PrefixPC
