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
  [opAt 548 .JUMPDEST,
   pushAt 549 5 137506062208,
   pushAt 550 1 68,
   opAt 551 .CALLDATALOAD,
   opAt 552 .SUB,
   pushAt 553 2 533,
   opAt 554 .JUMPI]

/-- The size test (`1 - bsize`, `2 - esize`, `word100`): fourteen instructions
ending in the second miss branch. -/
def tailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 555 0 0,
   opAt 556 .CALLDATALOAD,
   pushAt 557 1 1,
   opAt 558 .SUB,
   pushAt 559 1 32,
   opAt 560 .CALLDATALOAD,
   pushAt 561 1 2,
   opAt 562 .SUB,
   opAt 563 .OR,
   pushAt 564 1 100,
   opAt 565 .CALLDATALOAD,
   opAt 566 .OR,
   pushAt 567 2 533,
   opAt 568 .JUMPI]

def hitPrePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 569 .JUMPDEST,
   pushAt 570 2 65535,
   pushAt 571 1 3]

def hitPostPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 573 0 0,
   opAt 574 .MSTORE,
   pushAt 575 1 32,
   pushAt 576 0 0,
   opAt 577 .RETURN]

/-- The `EXP`, kept as a located witness so its opcode and fork availability are
discharged from the artifact like every other one. -/
def expAt : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  opAt 572 .EXP

@[simp] theorem widthPCs (i : Nat) (hi : 548 ≤ i) (hii : i ≤ 554) :
    Artifact.submissionArtifact.instructionPC i =
      ([765, 766, 772, 774, 775, 776, 779] : List Nat)[i - 548]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem tailPCs (i : Nat) (hi : 555 ≤ i) (hii : i ≤ 568) :
    Artifact.submissionArtifact.instructionPC i =
      ([780, 781, 782, 784, 785, 787, 788, 790, 791, 792, 794, 795, 796, 799] : List Nat)[i - 555]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem answerPCs (i : Nat) (hi : 569 ≤ i) (hii : i ≤ 577) :
    Artifact.submissionArtifact.instructionPC i =
      ([800, 801, 804, 806, 807, 808, 809, 811, 812] : List Nat)[i - 569]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

/-- The legacy entry, where both miss exits land. -/
theorem jumpDestLegacy :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 533 = true :=
  Artifact.isValidJumpDest_index 372 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
