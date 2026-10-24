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
  [pushAt 493 5 137506062208,
   pushAt 494 1 68,
   opAt 495 .CALLDATALOAD,
   opAt 496 .SUB,
   pushAt 497 2 533,
   opAt 498 .JUMPI]

/-- The size test (`1 - bsize`, `2 - esize`, `word100`): fourteen instructions
ending in the second miss branch. -/
def tailPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
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
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 513 2 65535,
   pushAt 514 1 3]

def hitPostPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 516 0 0,
   opAt 517 .MSTORE,
   pushAt 518 1 32,
   pushAt 519 0 0,
   opAt 520 .RETURN]

/-- The `EXP`, kept as a located witness so its opcode and fork availability are
discharged from the artifact like every other one. -/
def expAt : Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  opAt 515 .EXP

@[simp] theorem widthPCs (i : Nat) (hi : 493 ≤ i) (hii : i ≤ 498) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([699, 705, 707, 708, 709, 712] : List Nat)[i - 493]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem tailPCs (i : Nat) (hi : 499 ≤ i) (hii : i ≤ 512) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([713, 714, 715, 717, 718, 720, 721, 723, 724, 725, 727, 728, 729, 732] : List Nat)[i - 499]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem answerPCs (i : Nat) (hi : 513 ≤ i) (hii : i ≤ 520) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([733, 736, 738, 739, 740, 741, 743, 744] : List Nat)[i - 513]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

/-- The legacy entry, where both miss exits land. -/
theorem jumpDestLegacy :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 533 = true :=
  CycleSubmission.Global.Binding.jumpDest 370 (by rfl)

end CycleSubmission.Global.Memo
