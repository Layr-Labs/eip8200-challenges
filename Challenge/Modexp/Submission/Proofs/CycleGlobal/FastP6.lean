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
  [opAt 2636 .JUMPDEST,
   opAt 2637 (.Dup ⟨0,by decide⟩),
   pushAt 2638 2 10760,
   opAt 2639 .JUMPI]


/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2636 .JUMPDEST,
   opAt 2637 (.Dup ⟨0,by decide⟩),
   pushAt 2638 2 10760,
   opAt 2639 .JUMPI,
   pushAt 2640 0 0,
   opAt 2641 .RETURN]


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
  [opAt 2605 .JUMPDEST,
   pushAt 2606 1 32,
   opAt 2607 .CALLDATALOAD,
   pushAt 2608 2 673,
   opAt 2609 .JUMPI,
   opAt 475 .JUMPDEST]

def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2605 .JUMPDEST,
   pushAt 2606 1 32,
   opAt 2607 .CALLDATALOAD,
   pushAt 2608 2 673,
   opAt 2609 .JUMPI,
   pushAt 2610 1 64,
   opAt 2611 .CALLDATALOAD,
   opAt 2612 (.Dup ⟨0,by decide⟩),
   pushAt 2613 1 32,
   opAt 2614 .LT,
   pushAt 2615 2 10754,
   opAt 2616 .JUMPI,
   opAt 8410 .JUMPDEST,
   opAt 8411 .POP,
   pushAt 8412 2 673,
   opAt 8413 .JUMP,
   opAt 475 .JUMPDEST]

def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2605 .JUMPDEST,
   pushAt 2606 1 32,
   opAt 2607 .CALLDATALOAD,
   pushAt 2608 2 673,
   opAt 2609 .JUMPI,
   pushAt 2610 1 64,
   opAt 2611 .CALLDATALOAD,
   opAt 2612 (.Dup ⟨0,by decide⟩),
   pushAt 2613 1 32,
   opAt 2614 .LT,
   pushAt 2615 2 10754,
   opAt 2616 .JUMPI,
   pushAt 2617 0 0,
   opAt 2618 .CALLDATALOAD,
   pushAt 2619 1 96,
   opAt 2620 .ADD,
   opAt 2621 .CALLDATALOAD,
   opAt 2622 (.Dup ⟨1,by decide⟩),
   pushAt 2623 1 32,
   opAt 2624 .SUB,
   pushAt 2625 1 3,
   opAt 2626 .SHL,
   opAt 2627 .SHR,
   pushAt 2628 1 1,
   opAt 2629 .LT,
   pushAt 2630 0 0,
   opAt 2631 .MSTORE]

def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2632 (.Dup ⟨0,by decide⟩),
   opAt 2633 .MSIZE,
   opAt 2634 .SUB,
   opAt 2635 .RETURN]

theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3313 = true :=
  CycleSubmission.Global.Binding.jumpDest 2605 (by rfl)

theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10754 = true :=
  CycleSubmission.Global.Binding.jumpDest 8410 (by rfl)

@[simp] theorem packedEmptyPCs (i : Nat) (hi : 2636 ≤ i) (hii : i ≤ 2641) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3355,3356,3357,3360,3361,3362] : List Nat)[i - 2636]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem packedHeadPCs (i : Nat) (hi : 2605 ≤ i) (hii : i ≤ 2635) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3313,3314,3316,3317,3320,3321,3323,3324,3325,3327,3328,3331,3332,3333,3334,3336,3337,3338,3339,3341,3342,3344,3345,3346,3348,3349,3350,3351,3352,3353,3354] : List Nat)[i - 2605]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem packedTailPCs (i : Nat) (hi : 2617 ≤ i) (hii : i ≤ 2635) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3332,3333,3334,3336,3337,3338,3339,3341,3342,3344,3345,3346,3348,3349,3350,3351,3352,3353,3354] : List Nat)[i - 2617]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8410 ≤ i) (hii : i ≤ 8413) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10754,10755,10756,10759] : List Nat)[i - 8410]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl


def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8414 .JUMPDEST,
   pushAt 8415 1 12,
   opAt 8416 .XOR,
   pushAt 8417 2 3313,
   opAt 8418 .JUMPI]

def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8414 .JUMPDEST,
   pushAt 8415 1 12,
   opAt 8416 .XOR,
   pushAt 8417 2 3313,
   opAt 8418 .JUMPI,
   pushAt 8419 0 0,
   opAt 8420 .CALLDATALOAD,
   pushAt 8421 1 32,
   opAt 8422 .CALLDATALOAD,
   opAt 8423 .ADD,
   pushAt 8424 1 96,
   opAt 8425 .ADD,
   opAt 8426 .CALLDATALOAD,
   pushAt 8427 1 160,
   opAt 8428 .SHR,
   pushAt 8429 2 673,
   opAt 8430 .JUMPI,
   opAt 475 .JUMPDEST]

def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8414 .JUMPDEST,
   pushAt 8415 1 12,
   opAt 8416 .XOR,
   pushAt 8417 2 3313,
   opAt 8418 .JUMPI,
   pushAt 8419 0 0,
   opAt 8420 .CALLDATALOAD,
   pushAt 8421 1 32,
   opAt 8422 .CALLDATALOAD,
   opAt 8423 .ADD,
   pushAt 8424 1 96,
   opAt 8425 .ADD,
   opAt 8426 .CALLDATALOAD,
   pushAt 8427 1 160,
   opAt 8428 .SHR,
   pushAt 8429 2 673,
   opAt 8430 .JUMPI,
   pushAt 8431 1 12,
   pushAt 8432 0 0,
   opAt 8433 .RETURN]

theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10760 = true :=
  CycleSubmission.Global.Binding.jumpDest 8414 (by rfl)

@[simp] theorem packedZero12PCs (i : Nat) (hi : 8414 ≤ i) (hii : i ≤ 8434) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10760,10761,10763,10764,10767,10768,10769,10770,10772,10773,10774,10776,10777,10778,10780,10781,10784,10785,10787,10788,10789] : List Nat)[i - 8414]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

end CycleSubmission.Global.Fast
