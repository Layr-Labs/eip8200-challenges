import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 6 (instructions 1396..1368). -/

namespace CycleSubmission.Global.Fast
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 483..486, pc 692..696. -/
def blk1333 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 470 (.Dup ⟨4,by decide⟩),
   pushAt 471 1 1,
   pushAt 472 0 0,
   opAt 473 .RETURN]

/-- The empty-modulus test at pc 3482 (instructions 511..513, in the former unreachable
filler behind the memo hit exit) for a nonzero `msize`: `JUMPDEST PUSH2 3437 JUMPI`
consumes `msize` and lands on the zero-exponent test appended at pc 3437 with an
empty stack. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2669 .JUMPDEST,
   opAt 2670 (.Dup ⟨0,by decide⟩),
   pushAt 2671 2 10955,
   opAt 2672 .JUMPI]


/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2669 .JUMPDEST,
   opAt 2670 (.Dup ⟨0,by decide⟩),
   pushAt 2671 2 10955,
   opAt 2672 .JUMPI,
   pushAt 2673 0 0,
   opAt 2674 .RETURN]


/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- The zero-exponent test appended at pc 3437 (instructions 8638..8642) for a nonzero
`esize`: `JUMPDEST PUSH1 32 CALLDATALOAD PUSH2 698 JUMPI` lands on the `JUMPDEST` at
pc 698 (instruction 488), which falls into the fixed-vector recogniser at pc 699 with an
empty stack. -/
def blkZeroExpMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2635 .JUMPDEST,
   pushAt 2636 1 32,
   opAt 2637 .CALLDATALOAD,
   pushAt 2638 2 673,
   opAt 2639 .JUMPI,
   opAt 475 .JUMPDEST]

def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2635 .JUMPDEST,
   pushAt 2636 1 32,
   opAt 2637 .CALLDATALOAD,
   pushAt 2638 2 673,
   opAt 2639 .JUMPI,
   pushAt 2640 1 64,
   opAt 2641 .CALLDATALOAD,
   opAt 2642 (.Dup ⟨0,by decide⟩),
   pushAt 2643 1 32,
   opAt 2644 .LT,
   pushAt 2645 2 10949,
   opAt 2646 .JUMPI,
   opAt 8434 .JUMPDEST,
   opAt 8435 .POP,
   pushAt 8436 2 673,
   opAt 8437 .JUMP,
   opAt 475 .JUMPDEST]

def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2635 .JUMPDEST,
   pushAt 2636 1 32,
   opAt 2637 .CALLDATALOAD,
   pushAt 2638 2 673,
   opAt 2639 .JUMPI,
   pushAt 2640 1 64,
   opAt 2641 .CALLDATALOAD,
   opAt 2642 (.Dup ⟨0,by decide⟩),
   pushAt 2643 1 32,
   opAt 2644 .LT,
   pushAt 2645 2 10949,
   opAt 2646 .JUMPI,
   pushAt 2647 0 0,
   opAt 2648 .CALLDATALOAD,
   pushAt 2649 1 96,
   opAt 2650 .ADD,
   opAt 2651 .CALLDATALOAD,
   opAt 2652 (.Dup ⟨1,by decide⟩),
   pushAt 2653 1 32,
   opAt 2654 .SUB,
   pushAt 2655 1 3,
   opAt 2656 .SHL,
   opAt 2657 .SHR,
   pushAt 2658 1 1,
   opAt 2659 .LT,
   pushAt 2660 0 0,
   opAt 2661 .MSTORE]

def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2662 (.Dup ⟨0,by decide⟩),
   opAt 2663 .MSIZE,
   opAt 2664 .SUB,
   opAt 2665 .RETURN]

theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3416 = true :=
  CycleSubmission.Global.Binding.jumpDest 2635 (by rfl)

theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10949 = true :=
  CycleSubmission.Global.Binding.jumpDest 8434 (by rfl)

@[simp] theorem packedEmptyPCs (i : Nat) (hi : 2669 ≤ i) (hii : i ≤ 2674) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3461, 3462, 3463, 3466, 3467, 3468] : List Nat)[i - 2669]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem packedHeadPCs (i : Nat) (hi : 2635 ≤ i) (hii : i ≤ 2665) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3416, 3417, 3419, 3420, 3423, 3424, 3426, 3427, 3428, 3430, 3431, 3434, 3435, 3436, 3437, 3439, 3440, 3441, 3442, 3444, 3445, 3447, 3448, 3449, 3451, 3452, 3453, 3454, 3455, 3456, 3457] : List Nat)[i - 2635]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem packedTailPCs (i : Nat) (hi : 2647 ≤ i) (hii : i ≤ 2665) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3435, 3436, 3437, 3439, 3440, 3441, 3442, 3444, 3445, 3447, 3448, 3449, 3451, 3452, 3453, 3454, 3455, 3456, 3457] : List Nat)[i - 2647]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8434 ≤ i) (hii : i ≤ 8437) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10949, 10950, 10951, 10954] : List Nat)[i - 8434]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl


def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8438 .JUMPDEST,
   pushAt 8439 1 12,
   opAt 8440 .XOR,
   pushAt 8441 2 3416,
   opAt 8442 .JUMPI]

def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8438 .JUMPDEST,
   pushAt 8439 1 12,
   opAt 8440 .XOR,
   pushAt 8441 2 3416,
   opAt 8442 .JUMPI,
   pushAt 8443 0 0,
   opAt 8444 .CALLDATALOAD,
   pushAt 8445 1 32,
   opAt 8446 .CALLDATALOAD,
   opAt 8447 .ADD,
   pushAt 8448 1 96,
   opAt 8449 .ADD,
   opAt 8450 .CALLDATALOAD,
   pushAt 8451 1 160,
   opAt 8452 .SHR,
   pushAt 8453 2 673,
   opAt 8454 .JUMPI,
   opAt 475 .JUMPDEST]

def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8438 .JUMPDEST,
   pushAt 8439 1 12,
   opAt 8440 .XOR,
   pushAt 8441 2 3416,
   opAt 8442 .JUMPI,
   pushAt 8443 0 0,
   opAt 8444 .CALLDATALOAD,
   pushAt 8445 1 32,
   opAt 8446 .CALLDATALOAD,
   opAt 8447 .ADD,
   pushAt 8448 1 96,
   opAt 8449 .ADD,
   opAt 8450 .CALLDATALOAD,
   pushAt 8451 1 160,
   opAt 8452 .SHR,
   pushAt 8453 2 673,
   opAt 8454 .JUMPI,
   pushAt 8455 1 12,
   pushAt 8456 0 0,
   opAt 8457 .RETURN]

theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10955 = true :=
  CycleSubmission.Global.Binding.jumpDest 8438 (by rfl)

@[simp] theorem packedZero12PCs (i : Nat) (hi : 8438 ≤ i) (hii : i ≤ 8460) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10955, 10956, 10958, 10959, 10962, 10963, 10964, 10965, 10967, 10968, 10969, 10971, 10972, 10973, 10975, 10976, 10979, 10980, 10982, 10983, 10984, 10985, 10986] : List Nat)[i - 8438]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

end CycleSubmission.Global.Fast
