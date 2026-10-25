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
    (((CycleSubmission.Artifact.instructions.drop 370).take (1869-370)).map width) =
    (((Artifact.submissionInstructions.drop 370).take (1869-370)).map width) := by rfl

/-- Instruction addresses in the unchanged dispatch/conversion prefix agree
with the accepted proof base, despite changed destination literals. -/
@[simp] theorem eq_old (i : Nat) (hlo : 370 ≤ i) (hhi : i ≤ 1869) :
    CycleSubmission.Artifact.artifact.instructionPC i = Artifact.submissionArtifact.instructionPC i := by
  have h : (((CycleSubmission.Artifact.instructions.drop 370).take (i-370)).map width) =
      (((Artifact.submissionInstructions.drop 370).take (i-370)).map width) := by
    have h := congrArg (List.take (i-370)) widths_eq
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-370 ≤ 1869-370 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 370 = 533 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 370 = 533 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 370+(i-370)=i := by omega
  rw [← hi, pc_add, pc_add, ha, hb]
  change 533 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 370).take (i-370)) =
    533 + PCFast.byteLength ((Artifact.submissionInstructions.drop 370).take (i-370))
  rw [length_eq, length_eq, h]


private theorem suffix_widths_eq :
    (((CycleSubmission.Artifact.instructions.drop 1872).take (1953-1872)).map width) =
    (((Artifact.submissionInstructions.drop 1873).take (1954-1873)).map width) := by rfl

/-- After the shortened fixed caller, instruction indexes shift by one but all
    byte addresses and destination literals remain unchanged. -/
@[simp] theorem eq_old_tail (i : Nat) (hlo : 1872 ≤ i) (hhi : i ≤ 1953) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+1) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 1872).take (i-1872)).map width) =
      (((Artifact.submissionInstructions.drop 1873).take (i-1872)).map width) := by
    have h := congrArg (List.take (i-1872)) suffix_widths_eq
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-1872 ≤ 1953-1872 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 1872 = 2377 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 1873 = 2377 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 1872+(i-1872)=i := by omega
  have hj : 1873+(i-1872)=i+1 := by omega
  rw [← hi, pc_add, ha]
  rw [show 1872+(i-1872)+1 = 1873+(i-1872) by omega, pc_add, hb]
  change 2377 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 1872).take (i-1872)) =
    2377 + PCFast.byteLength ((Artifact.submissionInstructions.drop 1873).take (i-1872))
  rw [length_eq, length_eq, h]

private theorem suffix_widths_eq2 :
    (((CycleSubmission.Artifact.instructions.drop 1954).take (2531-1954)).map width) =
    (((Artifact.submissionInstructions.drop 1956).take (2533-1956)).map width) := by rfl

@[simp] theorem eq_old_tail2 (i : Nat) (hlo : 1954 ≤ i) (hhi : i ≤ 2531) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+2) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 1954).take (i-1954)).map width) =
      (((Artifact.submissionInstructions.drop 1956).take (i-1954)).map width) := by
    have h := congrArg (List.take (i-1954)) suffix_widths_eq2
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-1954 ≤ 2531-1954 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 1954 = 2506 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 1956 = 2506 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 1954+(i-1954)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 1954+(i-1954)+2 = 1956+(i-1954) by omega, pc_add, hb]
  change 2506 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 1954).take (i-1954)) =
    2506 + PCFast.byteLength ((Artifact.submissionInstructions.drop 1956).take (i-1954))
  rw [length_eq, length_eq, h]

end CycleSubmission.Global.PrefixPC
