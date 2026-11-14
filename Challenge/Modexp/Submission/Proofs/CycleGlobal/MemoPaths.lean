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
  [pushAt 646 5 137506062208,
   pushAt 647 1 68,
   opAt 648 .CALLDATALOAD,
   opAt 649 .SUB,
   pushAt 650 2 519,
   opAt 651 .JUMPI]

/-- The size test (`1 - bsize`, `2 - esize`, `word100`): fourteen instructions
ending in the second miss branch. -/
def tailPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 652 0 0,
   opAt 653 .CALLDATALOAD,
   pushAt 654 1 1,
   opAt 655 .SUB,
   pushAt 656 1 32,
   opAt 657 .CALLDATALOAD,
   pushAt 658 1 2,
   opAt 659 .SUB,
   opAt 660 .OR,
   pushAt 661 1 100,
   opAt 662 .CALLDATALOAD,
   opAt 663 .OR,
   pushAt 664 2 519,
   opAt 665 .JUMPI]

@[simp] theorem widthPCs (i : Nat) (hi : 646 ≤ i) (hii : i ≤ 651) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([912,918,920,921,922,925] : List Nat)[i - 646]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem tailPCs (i : Nat) (hi : 652 ≤ i) (hii : i ≤ 665) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([926,927,928,930,931,933,934,936,937,938,940,941,942,945] : List Nat)[i - 652]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDestLegacy :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 519 = true :=
  CycleSubmission.Global.Binding.jumpDest 357 (by rfl)

end CycleSubmission.Global.Memo
