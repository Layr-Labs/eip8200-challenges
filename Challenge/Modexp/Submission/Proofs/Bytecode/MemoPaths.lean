import Challenge.Modexp.Submission.Proofs.Bytecode.DispatchDefs
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

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Memo

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

/-- The word test (`word68 - K`): seven instructions ending in the first miss
branch. -/
def widthPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 493 5 137506062208,
   pushAt 494 1 68,
   opAt 495 .CALLDATALOAD,
   opAt 496 .SUB,
   pushAt 497 2 533,
   opAt 498 .JUMPI]

/-- The size test (`1 - bsize`, `2 - esize`, `word100`): fourteen instructions
ending in the second miss branch. -/
def tailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 499 0 0,
   opAt 500 .CALLDATALOAD,
   pushAt 501 1 1,
   opAt 502 .SUB,
   pushAt 503 1 32,
   opAt 504 .CALLDATALOAD,
   pushAt 505 1 2,
   opAt 506 .SUB,
   opAt 507 .OR,
   pushAt 508 1 100,
   opAt 509 .CALLDATALOAD,
   opAt 510 .OR,
   pushAt 511 2 533,
   opAt 512 .JUMPI]

def hitPrePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 513 2 8616,
   opAt 514 .JUMP]

def hitPostPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 6727 .JUMPDEST,
   pushAt 6728 32 26689440342447178617115869845918039756797228267049433585260346420242739014315,
   pushAt 6729 0 0,
   opAt 6730 .MSTORE,
   pushAt 6731 1 32,
   pushAt 6732 0 0,
   opAt 6733 .RETURN]

@[simp] theorem widthPCs (i : Nat) (hi : 493 ≤ i) (hii : i ≤ 498) :
    Artifact.submissionArtifact.instructionPC i =
      ([699, 705, 707, 708, 709, 712] : List Nat)[i - 493]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem tailPCs (i : Nat) (hi : 499 ≤ i) (hii : i ≤ 512) :
    Artifact.submissionArtifact.instructionPC i =
      ([713, 714, 715, 717, 718, 720, 721, 723, 724, 725, 727, 728, 729, 732] : List Nat)[i - 499]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem answerPCs (i : Nat) (hi : 513 ≤ i) (hii : i ≤ 520) :
    Artifact.submissionArtifact.instructionPC i =
      ([733, 736, 737, 739, 740, 741, 743, 744] : List Nat)[i - 513]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

/-- The legacy entry, where both miss exits land. -/
theorem jumpDestLegacy :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 533 = true :=
  Artifact.isValidJumpDest_index 370 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
