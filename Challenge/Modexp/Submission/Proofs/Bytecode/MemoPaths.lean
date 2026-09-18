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
  [opAt 572 .JUMPDEST,
   pushAt 573 5 137506062208,
   pushAt 574 1 68,
   opAt 575 .CALLDATALOAD,
   opAt 576 .SUB,
   pushAt 577 2 599,
   opAt 578 .JUMPI]

/-- The size test (`1 - bsize`, `2 - esize`, `word100`): fourteen instructions
ending in the second miss branch. -/
def tailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 579 0 0,
   opAt 580 .CALLDATALOAD,
   pushAt 581 1 1,
   opAt 582 .SUB,
   pushAt 583 1 32,
   opAt 584 .CALLDATALOAD,
   pushAt 585 1 2,
   opAt 586 .SUB,
   opAt 587 .OR,
   pushAt 588 1 100,
   opAt 589 .CALLDATALOAD,
   opAt 590 .OR,
   pushAt 591 2 599,
   opAt 592 .JUMPI]

def hitPrePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 593 .JUMPDEST,
   pushAt 594 2 65535,
   pushAt 595 1 3]

def hitPostPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 597 0 0,
   opAt 598 .MSTORE,
   pushAt 599 1 32,
   pushAt 600 0 0,
   opAt 601 .RETURN]

/-- The `EXP`, kept as a located witness so its opcode and fork availability are
discharged from the artifact like every other one. -/
def expAt : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  opAt 596 .EXP

@[simp] theorem widthPCs (i : Nat) (hi : 572 ≤ i) (hii : i ≤ 578) :
    Artifact.submissionArtifact.instructionPC i =
      ([795, 796, 802, 804, 805, 806, 809] : List Nat)[i - 572]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem tailPCs (i : Nat) (hi : 579 ≤ i) (hii : i ≤ 592) :
    Artifact.submissionArtifact.instructionPC i =
      ([810, 811, 812, 814, 815, 817, 818, 820, 821, 822, 824, 825, 826, 829] : List Nat)[i - 579]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem answerPCs (i : Nat) (hi : 593 ≤ i) (hii : i ≤ 601) :
    Artifact.submissionArtifact.instructionPC i =
      ([830, 831, 834, 836, 837, 838, 839, 841, 842] : List Nat)[i - 593]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

/-- The legacy entry, where both miss exits land. -/
theorem jumpDestLegacy :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 599 = true :=
  Artifact.isValidJumpDest_index 423 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
