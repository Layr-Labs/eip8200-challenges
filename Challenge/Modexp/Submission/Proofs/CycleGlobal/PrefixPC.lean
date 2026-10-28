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
    (((CycleSubmission.Artifact.instructions.drop 370).take (448-370)).map width) =
    (((Artifact.submissionInstructions.drop 370).take (448-370)).map width) := by rfl

/-- Instruction addresses in the unchanged dispatch/conversion prefix agree
with the accepted proof base, despite changed destination literals. -/
@[simp] theorem eq_old (i : Nat) (hlo : 370 ≤ i) (hhi : i ≤ 448) :
    CycleSubmission.Artifact.artifact.instructionPC i = Artifact.submissionArtifact.instructionPC i := by
  have h : (((CycleSubmission.Artifact.instructions.drop 370).take (i-370)).map width) =
      (((Artifact.submissionInstructions.drop 370).take (i-370)).map width) := by
    have h := congrArg (List.take (i-370)) widths_eq
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-370 ≤ 448-370 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 370 = 533 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 370 = 533 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 370+(i-370)=i := by omega
  rw [← hi, pc_add, pc_add, ha, hb]
  change 533 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 370).take (i-370)) =
    533 + PCFast.byteLength ((Artifact.submissionInstructions.drop 370).take (i-370))
  rw [length_eq, length_eq, h]


/-- Past the head segment, instruction indexes differ from the accepted proof base by a
constant on each segment below, while every byte address agrees with it. -/
private theorem widths_eq_eq_old1 :
    (((CycleSubmission.Artifact.instructions.drop 449).take (452-449)).map width) =
    (((Artifact.submissionInstructions.drop 450).take (453-450)).map width) := by rfl

@[simp] theorem eq_old1 (i : Nat) (hlo : 449 ≤ i) (hhi : i ≤ 452) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+1) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 449).take (i-449)).map width) =
      (((Artifact.submissionInstructions.drop 450).take (i-449)).map width) := by
    have h := congrArg (List.take (i-449)) widths_eq_eq_old1
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-449 ≤ 452-449 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 449 = 638 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 450 = 638 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 449+(i-449)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 449+(i-449)+1 = 450+(i-449) by omega, pc_add, hb]
  change 638 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 449).take (i-449)) =
    638 + PCFast.byteLength ((Artifact.submissionInstructions.drop 450).take (i-449))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old2 :
    (((CycleSubmission.Artifact.instructions.drop 453).take (468-453)).map width) =
    (((Artifact.submissionInstructions.drop 455).take (470-455)).map width) := by rfl

@[simp] theorem eq_old2 (i : Nat) (hlo : 453 ≤ i) (hhi : i ≤ 468) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+2) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 453).take (i-453)).map width) =
      (((Artifact.submissionInstructions.drop 455).take (i-453)).map width) := by
    have h := congrArg (List.take (i-453)) widths_eq_eq_old2
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-453 ≤ 468-453 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 453 = 644 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 455 = 644 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 453+(i-453)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 453+(i-453)+2 = 455+(i-453) by omega, pc_add, hb]
  change 644 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 453).take (i-453)) =
    644 + PCFast.byteLength ((Artifact.submissionInstructions.drop 455).take (i-453))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old3 :
    (((CycleSubmission.Artifact.instructions.drop 469).take (480-469)).map width) =
    (((Artifact.submissionInstructions.drop 472).take (483-472)).map width) := by rfl

@[simp] theorem eq_old3 (i : Nat) (hlo : 469 ≤ i) (hhi : i ≤ 480) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+3) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 469).take (i-469)).map width) =
      (((Artifact.submissionInstructions.drop 472).take (i-469)).map width) := by
    have h := congrArg (List.take (i-469)) widths_eq_eq_old3
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-469 ≤ 480-469 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 469 = 670 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 472 = 670 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 469+(i-469)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 469+(i-469)+3 = 472+(i-469) by omega, pc_add, hb]
  change 670 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 469).take (i-469)) =
    670 + PCFast.byteLength ((Artifact.submissionInstructions.drop 472).take (i-469))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old4 :
    (((CycleSubmission.Artifact.instructions.drop 481).take (1865-481)).map width) =
    (((Artifact.submissionInstructions.drop 485).take (1869-485)).map width) := by rfl

@[simp] theorem eq_old4 (i : Nat) (hlo : 481 ≤ i) (hhi : i ≤ 1865) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+4) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 481).take (i-481)).map width) =
      (((Artifact.submissionInstructions.drop 485).take (i-481)).map width) := by
    have h := congrArg (List.take (i-481)) widths_eq_eq_old4
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-481 ≤ 1865-481 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 481 = 689 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 485 = 689 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 481+(i-481)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 481+(i-481)+4 = 485+(i-481) by omega, pc_add, hb]
  change 689 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 481).take (i-481)) =
    689 + PCFast.byteLength ((Artifact.submissionInstructions.drop 485).take (i-481))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old_tail5 :
    (((CycleSubmission.Artifact.instructions.drop 1868).take (1877-1868)).map width) =
    (((Artifact.submissionInstructions.drop 1873).take (1882-1873)).map width) := by rfl

@[simp] theorem eq_old_tail5 (i : Nat) (hlo : 1868 ≤ i) (hhi : i ≤ 1877) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+5) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 1868).take (i-1868)).map width) =
      (((Artifact.submissionInstructions.drop 1873).take (i-1868)).map width) := by
    have h := congrArg (List.take (i-1868)) widths_eq_eq_old_tail5
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-1868 ≤ 1877-1868 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 1868 = 2377 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 1873 = 2377 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 1868+(i-1868)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 1868+(i-1868)+5 = 1873+(i-1868) by omega, pc_add, hb]
  change 2377 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 1868).take (i-1868)) =
    2377 + PCFast.byteLength ((Artifact.submissionInstructions.drop 1873).take (i-1868))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old_tail6 :
    (((CycleSubmission.Artifact.instructions.drop 1878).take (1948-1878)).map width) =
    (((Artifact.submissionInstructions.drop 1884).take (1954-1884)).map width) := by rfl

@[simp] theorem eq_old_tail6 (i : Nat) (hlo : 1878 ≤ i) (hhi : i ≤ 1948) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+6) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 1878).take (i-1878)).map width) =
      (((Artifact.submissionInstructions.drop 1884).take (i-1878)).map width) := by
    have h := congrArg (List.take (i-1878)) widths_eq_eq_old_tail6
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-1878 ≤ 1948-1878 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 1878 = 2397 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 1884 = 2397 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 1878+(i-1878)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 1878+(i-1878)+6 = 1884+(i-1878) by omega, pc_add, hb]
  change 2397 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 1878).take (i-1878)) =
    2397 + PCFast.byteLength ((Artifact.submissionInstructions.drop 1884).take (i-1878))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old_tail7 :
    (((CycleSubmission.Artifact.instructions.drop 1949).take (1954-1949)).map width) =
    (((Artifact.submissionInstructions.drop 1956).take (1961-1956)).map width) := by rfl

@[simp] theorem eq_old_tail7 (i : Nat) (hlo : 1949 ≤ i) (hhi : i ≤ 1954) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+7) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 1949).take (i-1949)).map width) =
      (((Artifact.submissionInstructions.drop 1956).take (i-1949)).map width) := by
    have h := congrArg (List.take (i-1949)) widths_eq_eq_old_tail7
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-1949 ≤ 1954-1949 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 1949 = 2506 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 1956 = 2506 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 1949+(i-1949)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 1949+(i-1949)+7 = 1956+(i-1949) by omega, pc_add, hb]
  change 2506 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 1949).take (i-1949)) =
    2506 + PCFast.byteLength ((Artifact.submissionInstructions.drop 1956).take (i-1949))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old_tail8 :
    (((CycleSubmission.Artifact.instructions.drop 1955).take (2012-1955)).map width) =
    (((Artifact.submissionInstructions.drop 1963).take (2020-1963)).map width) := by rfl

@[simp] theorem eq_old_tail8 (i : Nat) (hlo : 1955 ≤ i) (hhi : i ≤ 2012) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+8) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 1955).take (i-1955)).map width) =
      (((Artifact.submissionInstructions.drop 1963).take (i-1955)).map width) := by
    have h := congrArg (List.take (i-1955)) widths_eq_eq_old_tail8
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-1955 ≤ 2012-1955 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 1955 = 2518 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 1963 = 2518 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 1955+(i-1955)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 1955+(i-1955)+8 = 1963+(i-1955) by omega, pc_add, hb]
  change 2518 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 1955).take (i-1955)) =
    2518 + PCFast.byteLength ((Artifact.submissionInstructions.drop 1963).take (i-1955))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old_tail10 :
    (((CycleSubmission.Artifact.instructions.drop 2013).take (2024-2013)).map width) =
    (((Artifact.submissionInstructions.drop 2023).take (2034-2023)).map width) := by rfl

@[simp] theorem eq_old_tail10 (i : Nat) (hlo : 2013 ≤ i) (hhi : i ≤ 2024) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+10) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 2013).take (i-2013)).map width) =
      (((Artifact.submissionInstructions.drop 2023).take (i-2013)).map width) := by
    have h := congrArg (List.take (i-2013)) widths_eq_eq_old_tail10
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-2013 ≤ 2024-2013 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 2013 = 2592 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 2023 = 2592 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 2013+(i-2013)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 2013+(i-2013)+10 = 2023+(i-2013) by omega, pc_add, hb]
  change 2592 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 2013).take (i-2013)) =
    2592 + PCFast.byteLength ((Artifact.submissionInstructions.drop 2023).take (i-2013))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old_tail11 :
    (((CycleSubmission.Artifact.instructions.drop 2025).take (2128-2025)).map width) =
    (((Artifact.submissionInstructions.drop 2036).take (2139-2036)).map width) := by rfl

@[simp] theorem eq_old_tail11 (i : Nat) (hlo : 2025 ≤ i) (hhi : i ≤ 2128) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+11) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 2025).take (i-2025)).map width) =
      (((Artifact.submissionInstructions.drop 2036).take (i-2025)).map width) := by
    have h := congrArg (List.take (i-2025)) widths_eq_eq_old_tail11
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-2025 ≤ 2128-2025 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 2025 = 2609 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 2036 = 2609 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 2025+(i-2025)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 2025+(i-2025)+11 = 2036+(i-2025) by omega, pc_add, hb]
  change 2609 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 2025).take (i-2025)) =
    2609 + PCFast.byteLength ((Artifact.submissionInstructions.drop 2036).take (i-2025))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old_tail12 :
    (((CycleSubmission.Artifact.instructions.drop 2129).take (2521-2129)).map width) =
    (((Artifact.submissionInstructions.drop 2141).take (2533-2141)).map width) := by rfl

@[simp] theorem eq_old_tail12 (i : Nat) (hlo : 2129 ≤ i) (hhi : i ≤ 2521) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+12) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 2129).take (i-2129)).map width) =
      (((Artifact.submissionInstructions.drop 2141).take (i-2129)).map width) := by
    have h := congrArg (List.take (i-2129)) widths_eq_eq_old_tail12
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-2129 ≤ 2521-2129 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 2129 = 2769 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 2141 = 2769 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 2129+(i-2129)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 2129+(i-2129)+12 = 2141+(i-2129) by omega, pc_add, hb]
  change 2769 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 2129).take (i-2129)) =
    2769 + PCFast.byteLength ((Artifact.submissionInstructions.drop 2141).take (i-2129))
  rw [length_eq, length_eq, h]

end CycleSubmission.Global.PrefixPC
