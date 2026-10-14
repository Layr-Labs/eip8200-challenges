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
  [pushAt 495 5 137506062208,
   pushAt 496 1 68,
   opAt 497 .CALLDATALOAD,
   opAt 498 .SUB,
   pushAt 499 2 533,
   opAt 500 .JUMPI]

/-- The size test (`1 - bsize`, `2 - esize`, `word100`): fourteen instructions
ending in the second miss branch. -/
def tailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 501 0 0,
   opAt 502 .CALLDATALOAD,
   pushAt 503 1 1,
   opAt 504 .SUB,
   pushAt 505 1 32,
   opAt 506 .CALLDATALOAD,
   pushAt 507 1 2,
   opAt 508 .SUB,
   opAt 509 .OR,
   pushAt 510 1 100,
   opAt 511 .CALLDATALOAD,
   opAt 512 .OR,
   pushAt 513 2 533,
   opAt 514 .JUMPI]

def hitPrePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 515 2 65535,
   pushAt 516 1 3]

def hitPostPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 518 0 0,
   opAt 519 .MSTORE,
   pushAt 520 1 32,
   pushAt 521 0 0,
   opAt 522 .RETURN]

/-- The `EXP`, kept as a located witness so its opcode and fork availability are
discharged from the artifact like every other one. -/
def expAt : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  opAt 517 .EXP

@[simp] theorem widthPCs (i : Nat) (hi : 495 ≤ i) (hii : i ≤ 500) :
    Artifact.submissionArtifact.instructionPC i =
      ([699, 705, 707, 708, 709, 712] : List Nat)[i - 495]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem tailPCs (i : Nat) (hi : 501 ≤ i) (hii : i ≤ 514) :
    Artifact.submissionArtifact.instructionPC i =
      ([713, 714, 715, 717, 718, 720, 721, 723, 724, 725, 727, 728, 729, 732] : List Nat)[i - 501]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem answerPCs (i : Nat) (hi : 515 ≤ i) (hii : i ≤ 522) :
    Artifact.submissionArtifact.instructionPC i =
      ([733, 736, 738, 739, 740, 741, 743, 744] : List Nat)[i - 515]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

/-- The legacy entry, where both miss exits land. -/
theorem jumpDestLegacy :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 533 = true :=
  Artifact.isValidJumpDest_index 372 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
