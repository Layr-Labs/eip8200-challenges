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
  [opAt 2667 .JUMPDEST,
   opAt 2668 (.Dup ⟨0,by decide⟩),
   pushAt 2669 2 10955,
   opAt 2670 .JUMPI]


/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2667 .JUMPDEST,
   opAt 2668 (.Dup ⟨0,by decide⟩),
   pushAt 2669 2 10955,
   opAt 2670 .JUMPI,
   pushAt 2671 0 0,
   opAt 2672 .RETURN]


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
  [opAt 2633 .JUMPDEST,
   pushAt 2634 1 32,
   opAt 2635 .CALLDATALOAD,
   pushAt 2636 2 673,
   opAt 2637 .JUMPI,
   opAt 475 .JUMPDEST]

def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2633 .JUMPDEST,
   pushAt 2634 1 32,
   opAt 2635 .CALLDATALOAD,
   pushAt 2636 2 673,
   opAt 2637 .JUMPI,
   pushAt 2638 1 64,
   opAt 2639 .CALLDATALOAD,
   opAt 2640 (.Dup ⟨0,by decide⟩),
   pushAt 2641 1 32,
   opAt 2642 .LT,
   pushAt 2643 2 10949,
   opAt 2644 .JUMPI,
   opAt 8432 .JUMPDEST,
   opAt 8433 .POP,
   pushAt 8434 2 673,
   opAt 8435 .JUMP,
   opAt 475 .JUMPDEST]

def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2633 .JUMPDEST,
   pushAt 2634 1 32,
   opAt 2635 .CALLDATALOAD,
   pushAt 2636 2 673,
   opAt 2637 .JUMPI,
   pushAt 2638 1 64,
   opAt 2639 .CALLDATALOAD,
   opAt 2640 (.Dup ⟨0,by decide⟩),
   pushAt 2641 1 32,
   opAt 2642 .LT,
   pushAt 2643 2 10949,
   opAt 2644 .JUMPI,
   pushAt 2645 0 0,
   opAt 2646 .CALLDATALOAD,
   pushAt 2647 1 96,
   opAt 2648 .ADD,
   opAt 2649 .CALLDATALOAD,
   opAt 2650 (.Dup ⟨1,by decide⟩),
   pushAt 2651 1 32,
   opAt 2652 .SUB,
   pushAt 2653 1 3,
   opAt 2654 .SHL,
   opAt 2655 .SHR,
   pushAt 2656 1 1,
   opAt 2657 .LT,
   pushAt 2658 0 0,
   opAt 2659 .MSTORE]

def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2660 (.Dup ⟨0,by decide⟩),
   opAt 2661 .MSIZE,
   opAt 2662 .SUB,
   opAt 2663 .RETURN]

theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3416 = true :=
  CycleSubmission.Global.Binding.jumpDest 2633 (by rfl)

theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10949 = true :=
  CycleSubmission.Global.Binding.jumpDest 8432 (by rfl)

@[simp] theorem packedEmptyPCs (i : Nat) (hi : 2667 ≤ i) (hii : i ≤ 2672) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3461, 3462, 3463, 3466, 3467, 3468] : List Nat)[i - 2667]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem packedHeadPCs (i : Nat) (hi : 2633 ≤ i) (hii : i ≤ 2663) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3416, 3417, 3419, 3420, 3423, 3424, 3426, 3427, 3428, 3430, 3431, 3434, 3435, 3436, 3437, 3439, 3440, 3441, 3442, 3444, 3445, 3447, 3448, 3449, 3451, 3452, 3453, 3454, 3455, 3456, 3457] : List Nat)[i - 2633]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem packedTailPCs (i : Nat) (hi : 2645 ≤ i) (hii : i ≤ 2663) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3435, 3436, 3437, 3439, 3440, 3441, 3442, 3444, 3445, 3447, 3448, 3449, 3451, 3452, 3453, 3454, 3455, 3456, 3457] : List Nat)[i - 2645]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8432 ≤ i) (hii : i ≤ 8435) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10949, 10950, 10951, 10954] : List Nat)[i - 8432]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl


def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8436 .JUMPDEST,
   pushAt 8437 1 12,
   opAt 8438 .XOR,
   pushAt 8439 2 3416,
   opAt 8440 .JUMPI]

def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8436 .JUMPDEST,
   pushAt 8437 1 12,
   opAt 8438 .XOR,
   pushAt 8439 2 3416,
   opAt 8440 .JUMPI,
   pushAt 8441 0 0,
   opAt 8442 .CALLDATALOAD,
   pushAt 8443 1 32,
   opAt 8444 .CALLDATALOAD,
   opAt 8445 .ADD,
   pushAt 8446 1 96,
   opAt 8447 .ADD,
   opAt 8448 .CALLDATALOAD,
   pushAt 8449 1 160,
   opAt 8450 .SHR,
   pushAt 8451 2 673,
   opAt 8452 .JUMPI,
   opAt 475 .JUMPDEST]

def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8436 .JUMPDEST,
   pushAt 8437 1 12,
   opAt 8438 .XOR,
   pushAt 8439 2 3416,
   opAt 8440 .JUMPI,
   pushAt 8441 0 0,
   opAt 8442 .CALLDATALOAD,
   pushAt 8443 1 32,
   opAt 8444 .CALLDATALOAD,
   opAt 8445 .ADD,
   pushAt 8446 1 96,
   opAt 8447 .ADD,
   opAt 8448 .CALLDATALOAD,
   pushAt 8449 1 160,
   opAt 8450 .SHR,
   pushAt 8451 2 673,
   opAt 8452 .JUMPI,
   pushAt 8453 1 12,
   pushAt 8454 0 0,
   opAt 8455 .RETURN]

theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10955 = true :=
  CycleSubmission.Global.Binding.jumpDest 8436 (by rfl)

@[simp] theorem packedZero12PCs (i : Nat) (hi : 8436 ≤ i) (hii : i ≤ 8458) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10955, 10956, 10958, 10959, 10962, 10963, 10964, 10965, 10967, 10968, 10969, 10971, 10972, 10973, 10975, 10976, 10979, 10980, 10982, 10983, 10984, 10985, 10986] : List Nat)[i - 8436]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

end CycleSubmission.Global.Fast
