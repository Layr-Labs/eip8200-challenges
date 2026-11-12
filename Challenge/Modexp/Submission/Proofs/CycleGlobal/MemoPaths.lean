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
  [pushAt 476 5 137506062208,
   pushAt 477 1 68,
   opAt 478 .CALLDATALOAD,
   opAt 479 .SUB,
   pushAt 480 2 519,
   opAt 481 .JUMPI]

/-- The size test (`1 - bsize`, `2 - esize`, `word100`): fourteen instructions
ending in the second miss branch. -/
def tailPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 482 0 0,
   opAt 483 .CALLDATALOAD,
   pushAt 484 1 1,
   opAt 485 .SUB,
   pushAt 486 1 32,
   opAt 487 .CALLDATALOAD,
   pushAt 488 1 2,
   opAt 489 .SUB,
   opAt 490 .OR,
   pushAt 491 1 100,
   opAt 492 .CALLDATALOAD,
   opAt 493 .OR,
   pushAt 494 2 519,
   opAt 495 .JUMPI]

@[simp] theorem widthPCs (i : Nat) (hi : 476 ≤ i) (hii : i ≤ 481) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([674, 680, 682, 683, 684, 687] : List Nat)[i - 476]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem tailPCs (i : Nat) (hi : 482 ≤ i) (hii : i ≤ 495) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([688, 689, 690, 692, 693, 695, 696, 698, 699, 700, 702, 703, 704, 707] : List Nat)[i - 482]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDestLegacy :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 519 = true :=
  CycleSubmission.Global.Binding.jumpDest 357 (by rfl)

end CycleSubmission.Global.Memo
