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

/-- Instruction indexes differ from the accepted proof base by a constant on each segment
below, while every byte address agrees with it. -/
private theorem widths_eq_eq_old :
    (((CycleSubmission.Artifact.instructions.drop 370).take (435-370)).map width) =
    (((Artifact.submissionInstructions.drop 370).take (435-370)).map width) := by rfl

@[simp] theorem eq_old (i : Nat) (hlo : 370 ≤ i) (hhi : i ≤ 435) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+0) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 370).take (i-370)).map width) =
      (((Artifact.submissionInstructions.drop 370).take (i-370)).map width) := by
    have h := congrArg (List.take (i-370)) widths_eq_eq_old
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-370 ≤ 435-370 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 370 = 533 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 370 = 533 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 370+(i-370)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 370+(i-370)+0 = 370+(i-370) by omega, pc_add, hb]
  change 533 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 370).take (i-370)) =
    533 + PCFast.byteLength ((Artifact.submissionInstructions.drop 370).take (i-370))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old2a :
    (((CycleSubmission.Artifact.instructions.drop 453).take (454-453)).map width) =
    (((Artifact.submissionInstructions.drop 455).take (456-455)).map width) := by rfl

@[simp] theorem eq_old2a (i : Nat) (hlo : 453 ≤ i) (hhi : i ≤ 454) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+2) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 453).take (i-453)).map width) =
      (((Artifact.submissionInstructions.drop 455).take (i-453)).map width) := by
    have h := congrArg (List.take (i-453)) widths_eq_eq_old2a
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-453 ≤ 454-453 by omega)] using h
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

private theorem widths_eq_eq_old2 :
    (((CycleSubmission.Artifact.instructions.drop 455).take (467-455)).map width) =
    (((Artifact.submissionInstructions.drop 458).take (470-458)).map width) := by rfl

@[simp] theorem eq_old2 (i : Nat) (hlo : 455 ≤ i) (hhi : i ≤ 467) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+3) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 455).take (i-455)).map width) =
      (((Artifact.submissionInstructions.drop 458).take (i-455)).map width) := by
    have h := congrArg (List.take (i-455)) widths_eq_eq_old2
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-455 ≤ 467-455 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 455 = 648 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 458 = 648 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 455+(i-455)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 455+(i-455)+3 = 458+(i-455) by omega, pc_add, hb]
  change 648 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 455).take (i-455)) =
    648 + PCFast.byteLength ((Artifact.submissionInstructions.drop 458).take (i-455))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old3 :
    (((CycleSubmission.Artifact.instructions.drop 468).take (479-468)).map width) =
    (((Artifact.submissionInstructions.drop 472).take (483-472)).map width) := by rfl

@[simp] theorem eq_old3 (i : Nat) (hlo : 468 ≤ i) (hhi : i ≤ 479) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+4) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 468).take (i-468)).map width) =
      (((Artifact.submissionInstructions.drop 472).take (i-468)).map width) := by
    have h := congrArg (List.take (i-468)) widths_eq_eq_old3
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-468 ≤ 479-468 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 468 = 670 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 472 = 670 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 468+(i-468)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 468+(i-468)+4 = 472+(i-468) by omega, pc_add, hb]
  change 670 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 468).take (i-468)) =
    670 + PCFast.byteLength ((Artifact.submissionInstructions.drop 472).take (i-468))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old3b :
    (((CycleSubmission.Artifact.instructions.drop 480).take (484-480)).map width) =
    (((Artifact.submissionInstructions.drop 485).take (489-485)).map width) := by rfl

@[simp] theorem eq_old3b (i : Nat) (hlo : 480 ≤ i) (hhi : i ≤ 484) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+5) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 480).take (i-480)).map width) =
      (((Artifact.submissionInstructions.drop 485).take (i-480)).map width) := by
    have h := congrArg (List.take (i-480)) widths_eq_eq_old3b
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-480 ≤ 484-480 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 480 = 689 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 485 = 689 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 480+(i-480)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 480+(i-480)+5 = 485+(i-480) by omega, pc_add, hb]
  change 689 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 480).take (i-480)) =
    689 + PCFast.byteLength ((Artifact.submissionInstructions.drop 485).take (i-480))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old4a :
    (((CycleSubmission.Artifact.instructions.drop 486).take (510-486)).map width) =
    (((Artifact.submissionInstructions.drop 490).take (514-490)).map width) := by rfl

/-- Up to the memo's hit exit (index 510, pc 736) the widths agree with the accepted base. -/
@[simp] theorem eq_old4a (i : Nat) (hlo : 486 ≤ i) (hhi : i ≤ 510) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+4) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 486).take (i-486)).map width) =
      (((Artifact.submissionInstructions.drop 490).take (i-486)).map width) := by
    have h := congrArg (List.take (i-486)) widths_eq_eq_old4a
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-486 ≤ 510-486 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 486 = 696 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 490 = 696 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 486+(i-486)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 486+(i-486)+4 = 490+(i-486) by omega, pc_add, hb]
  change 696 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 486).take (i-486)) =
    696 + PCFast.byteLength ((Artifact.submissionInstructions.drop 490).take (i-486))
  rw [length_eq, length_eq, h]

private theorem widths_eq_eq_old4 :
    (((CycleSubmission.Artifact.instructions.drop 517).take (1865-517)).map width) =
    (((Artifact.submissionInstructions.drop 521).take (1869-521)).map width) := by rfl

/-- From the window core's `JUMPDEST` (index 517, pc 745) on, the widths agree with the accepted
base again; the memo answer block before it keeps its byte length. -/
@[simp] theorem eq_old4 (i : Nat) (hlo : 517 ≤ i) (hhi : i ≤ 1865) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+4) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 517).take (i-517)).map width) =
      (((Artifact.submissionInstructions.drop 521).take (i-517)).map width) := by
    have h := congrArg (List.take (i-517)) widths_eq_eq_old4
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-517 ≤ 1865-517 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 517 = 745 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 521 = 745 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 517+(i-517)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 517+(i-517)+4 = 521+(i-517) by omega, pc_add, hb]
  change 745 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 517).take (i-517)) =
    745 + PCFast.byteLength ((Artifact.submissionInstructions.drop 521).take (i-517))
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
    (((CycleSubmission.Artifact.instructions.drop 2025).take (2057-2025)).map width) =
    (((Artifact.submissionInstructions.drop 2036).take (2068-2036)).map width) := by rfl

@[simp] theorem eq_old_tail11 (i : Nat) (hlo : 2025 ≤ i) (hhi : i ≤ 2057) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+11) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 2025).take (i-2025)).map width) =
      (((Artifact.submissionInstructions.drop 2036).take (i-2025)).map width) := by
    have h := congrArg (List.take (i-2025)) widths_eq_eq_old_tail11
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-2025 ≤ 2057-2025 by omega)] using h
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
    (((CycleSubmission.Artifact.instructions.drop 2137).take (2237-2137)).map width) =
    (((Artifact.submissionInstructions.drop 2159).take (2259-2159)).map width) := by rfl

@[simp] theorem eq_old_tail12 (i : Nat) (hlo : 2137 ≤ i) (hhi : i ≤ 2237) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      Artifact.submissionArtifact.instructionPC (i+22) := by
  have h : (((CycleSubmission.Artifact.instructions.drop 2137).take (i-2137)).map width) =
      (((Artifact.submissionInstructions.drop 2159).take (i-2137)).map width) := by
    have h := congrArg (List.take (i-2137)) widths_eq_eq_old_tail12
    simpa only [← List.map_take, List.take_take,
      Nat.min_eq_left (show i-2137 ≤ 2237-2137 by omega)] using h
  have ha : CycleSubmission.Artifact.artifact.instructionPC 2137 = 2787 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hb : Artifact.submissionArtifact.instructionPC 2159 = 2787 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  have hi : 2137+(i-2137)=i := by omega
  rw [← hi, pc_add, ha]
  rw [show 2137+(i-2137)+22 = 2159+(i-2137) by omega, pc_add, hb]
  change 2787 + PCFast.byteLength ((CycleSubmission.Artifact.instructions.drop 2137).take (i-2137)) =
    2787 + PCFast.byteLength ((Artifact.submissionInstructions.drop 2159).take (i-2137))
  rw [length_eq, length_eq, h]

end CycleSubmission.Global.PrefixPC
