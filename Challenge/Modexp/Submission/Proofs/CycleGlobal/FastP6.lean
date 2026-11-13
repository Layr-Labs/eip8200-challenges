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
  [opAt 2672 .JUMPDEST,
   opAt 2673 (.Dup ⟨0,by decide⟩),
   pushAt 2674 2 10955,
   opAt 2675 .JUMPI]


/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2672 .JUMPDEST,
   opAt 2673 (.Dup ⟨0,by decide⟩),
   pushAt 2674 2 10955,
   opAt 2675 .JUMPI,
   pushAt 2676 0 0,
   opAt 2677 .RETURN]


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
  [opAt 2638 .JUMPDEST,
   pushAt 2639 1 32,
   opAt 2640 .CALLDATALOAD,
   pushAt 2641 2 673,
   opAt 2642 .JUMPI,
   opAt 475 .JUMPDEST]

def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2638 .JUMPDEST,
   pushAt 2639 1 32,
   opAt 2640 .CALLDATALOAD,
   pushAt 2641 2 673,
   opAt 2642 .JUMPI,
   pushAt 2643 1 64,
   opAt 2644 .CALLDATALOAD,
   opAt 2645 (.Dup ⟨0,by decide⟩),
   pushAt 2646 1 32,
   opAt 2647 .LT,
   pushAt 2648 2 10949,
   opAt 2649 .JUMPI,
   opAt 8437 .JUMPDEST,
   opAt 8438 .POP,
   pushAt 8439 2 673,
   opAt 8440 .JUMP,
   opAt 475 .JUMPDEST]

def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2638 .JUMPDEST,
   pushAt 2639 1 32,
   opAt 2640 .CALLDATALOAD,
   pushAt 2641 2 673,
   opAt 2642 .JUMPI,
   pushAt 2643 1 64,
   opAt 2644 .CALLDATALOAD,
   opAt 2645 (.Dup ⟨0,by decide⟩),
   pushAt 2646 1 32,
   opAt 2647 .LT,
   pushAt 2648 2 10949,
   opAt 2649 .JUMPI,
   pushAt 2650 0 0,
   opAt 2651 .CALLDATALOAD,
   pushAt 2652 1 96,
   opAt 2653 .ADD,
   opAt 2654 .CALLDATALOAD,
   opAt 2655 (.Dup ⟨1,by decide⟩),
   pushAt 2656 1 32,
   opAt 2657 .SUB,
   pushAt 2658 1 3,
   opAt 2659 .SHL,
   opAt 2660 .SHR,
   pushAt 2661 1 1,
   opAt 2662 .LT,
   pushAt 2663 0 0,
   opAt 2664 .MSTORE]

def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2665 (.Dup ⟨0,by decide⟩),
   opAt 2666 .MSIZE,
   opAt 2667 .SUB,
   opAt 2668 .RETURN]

theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3416 = true :=
  CycleSubmission.Global.Binding.jumpDest 2638 (by rfl)

theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10949 = true :=
  CycleSubmission.Global.Binding.jumpDest 8437 (by rfl)

@[simp] theorem packedEmptyPCs (i : Nat) (hi : 2672 ≤ i) (hii : i ≤ 2677) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3461, 3462, 3463, 3466, 3467, 3468] : List Nat)[i - 2672]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem packedHeadPCs (i : Nat) (hi : 2638 ≤ i) (hii : i ≤ 2668) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3416, 3417, 3419, 3420, 3423, 3424, 3426, 3427, 3428, 3430, 3431, 3434, 3435, 3436, 3437, 3439, 3440, 3441, 3442, 3444, 3445, 3447, 3448, 3449, 3451, 3452, 3453, 3454, 3455, 3456, 3457] : List Nat)[i - 2638]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem packedTailPCs (i : Nat) (hi : 2650 ≤ i) (hii : i ≤ 2668) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3435, 3436, 3437, 3439, 3440, 3441, 3442, 3444, 3445, 3447, 3448, 3449, 3451, 3452, 3453, 3454, 3455, 3456, 3457] : List Nat)[i - 2650]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8437 ≤ i) (hii : i ≤ 8440) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10949, 10950, 10951, 10954] : List Nat)[i - 8437]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl


def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8441 .JUMPDEST,
   pushAt 8442 1 12,
   opAt 8443 .XOR,
   pushAt 8444 2 3416,
   opAt 8445 .JUMPI]

def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8441 .JUMPDEST,
   pushAt 8442 1 12,
   opAt 8443 .XOR,
   pushAt 8444 2 3416,
   opAt 8445 .JUMPI,
   pushAt 8446 0 0,
   opAt 8447 .CALLDATALOAD,
   pushAt 8448 1 32,
   opAt 8449 .CALLDATALOAD,
   opAt 8450 .ADD,
   pushAt 8451 1 96,
   opAt 8452 .ADD,
   opAt 8453 .CALLDATALOAD,
   pushAt 8454 1 160,
   opAt 8455 .SHR,
   pushAt 8456 2 673,
   opAt 8457 .JUMPI,
   opAt 475 .JUMPDEST]

def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8441 .JUMPDEST,
   pushAt 8442 1 12,
   opAt 8443 .XOR,
   pushAt 8444 2 3416,
   opAt 8445 .JUMPI,
   pushAt 8446 0 0,
   opAt 8447 .CALLDATALOAD,
   pushAt 8448 1 32,
   opAt 8449 .CALLDATALOAD,
   opAt 8450 .ADD,
   pushAt 8451 1 96,
   opAt 8452 .ADD,
   opAt 8453 .CALLDATALOAD,
   pushAt 8454 1 160,
   opAt 8455 .SHR,
   pushAt 8456 2 673,
   opAt 8457 .JUMPI,
   pushAt 8458 1 12,
   pushAt 8459 0 0,
   opAt 8460 .RETURN]

theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10955 = true :=
  CycleSubmission.Global.Binding.jumpDest 8441 (by rfl)

@[simp] theorem packedZero12PCs (i : Nat) (hi : 8441 ≤ i) (hii : i ≤ 8463) :
 CycleSubmission.Artifact.artifact.instructionPC i =
  ([10955, 10956, 10958, 10959, 10962, 10963, 10964, 10965, 10967, 10968, 10969, 10971, 10972, 10973, 10975, 10976, 10979, 10980, 10982, 10983, 10984, 10985, 10986] : List Nat)[i-8441]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

end CycleSubmission.Global.Fast
