import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.DispatchDefs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 400000
set_option maxHeartbeats 2000000

/-!
# Located instructions of the fixed-vector memo

The recogniser occupies pc 1064..1098 and the answer block pc 1099..1111,
inside the region the previous image used for the generic exponent loop that
no input reaches any more (every route into it now bails to `modexpBig`).

The recogniser is entered from the retargeted width-miss trampoline at pc 126
with an empty stack, so each of its two miss exits restores the legacy entry at
pc 598 by changing only the program counter.
-/

namespace CycleSubmission.Global.Memo
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM
open CycleSubmission.Global.Dispatch

/-- The word test (`word68 - K`): seven instructions ending in the first miss
branch. -/
def widthPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 489 5 137506062208,
   pushAt 490 1 68,
   opAt 491 .CALLDATALOAD,
   opAt 492 .SUB,
   pushAt 493 2 533,
   opAt 494 .JUMPI]

/-- The size test (`1 - bsize`, `2 - esize`, `word100`): fourteen instructions
ending in the second miss branch. -/
def tailPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 495 0 0,
   opAt 496 .CALLDATALOAD,
   pushAt 497 1 1,
   opAt 498 .SUB,
   pushAt 499 1 32,
   opAt 500 .CALLDATALOAD,
   pushAt 501 1 2,
   opAt 502 .SUB,
   opAt 503 .OR,
   pushAt 504 1 100,
   opAt 505 .CALLDATALOAD,
   opAt 506 .OR,
   pushAt 507 2 533,
   opAt 508 .JUMPI]

/-- The hit exit at pc 733: jump to the answer block at pc 60. -/
def hitPrePath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 509 2 60,
   opAt 510 .JUMP]

/-- The answer block at pc 60: push the precomputed `3^65535 mod 2^255`, store it and
return the word. -/
def hitPostPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 41 .JUMPDEST,
   pushAt 42 32 26689440342447178617115869845918039756797228267049433585260346420242739014315,
   pushAt 43 0 0,
   opAt 44 .MSTORE,
   pushAt 45 2 32,
   pushAt 46 0 0,
   opAt 47 .RETURN]

@[simp] theorem widthPCs (i : Nat) (hi : 489 ≤ i) (hii : i ≤ 494) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([699, 705, 707, 708, 709, 712] : List Nat)[i - 489]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem tailPCs (i : Nat) (hi : 495 ≤ i) (hii : i ≤ 508) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([713, 714, 715, 717, 718, 720, 721, 723, 724, 725, 727, 728, 729, 732] : List Nat)[i - 495]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem answerPCs (i : Nat) (hi : 509 ≤ i) (hii : i ≤ 516) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([733, 736, 737, 738, 739, 740, 741, 742] : List Nat)[i - 509]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem answerBlockPCs (i : Nat) (hi : 41 ≤ i) (hii : i ≤ 47) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([60, 61, 94, 95, 96, 99, 100] : List Nat)[i - 41]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

/-- The legacy entry, where both miss exits land. -/
theorem jumpDestLegacy :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 533 = true :=
  CycleSubmission.Global.Binding.jumpDest 370 (by rfl)

end CycleSubmission.Global.Memo
