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
  [pushAt 638 5 137506062208,
   pushAt 639 1 68,
   opAt 640 .CALLDATALOAD,
   opAt 641 .SUB,
   pushAt 642 2 519,
   opAt 643 .JUMPI]
/-- The size test (`1 - bsize`, `2 - esize`, `word100`): fourteen instructions
ending in the second miss branch. -/
def tailPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 644 0 0,
   opAt 645 .CALLDATALOAD,
   pushAt 646 1 1,
   opAt 647 .SUB,
   pushAt 648 1 32,
   opAt 649 .CALLDATALOAD,
   pushAt 650 1 2,
   opAt 651 .SUB,
   opAt 652 .OR,
   pushAt 653 1 100,
   opAt 654 .CALLDATALOAD,
   opAt 655 .OR,
   pushAt 656 2 519,
   opAt 657 .JUMPI]
@[simp] theorem widthPCs (i : Nat) (hi : 638 ≤ i) (hii : i ≤ 643) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([903,909,911,912,913,916] : List Nat)[i - 638]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem tailPCs (i : Nat) (hi : 644 ≤ i) (hii : i ≤ 657) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([917,918,919,921,922,924,925,927,928,929,931,932,933,936] : List Nat)[i - 644]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
theorem jumpDestLegacy :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 519 = true :=
  CycleSubmission.Global.Binding.jumpDest 357 (by rfl)
end CycleSubmission.Global.Memo
