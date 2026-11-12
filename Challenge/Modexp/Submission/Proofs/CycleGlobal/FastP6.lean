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
  [opAt 471 (.Dup ⟨4,by decide⟩),
   pushAt 472 1 1,
   pushAt 473 0 0,
   opAt 474 .RETURN]

/-- The empty-modulus test at pc 3482 (instructions 511..513, in the former unreachable
filler behind the memo hit exit) for a nonzero `msize`: `JUMPDEST PUSH2 3437 JUMPI`
consumes `msize` and lands on the zero-exponent test appended at pc 3437 with an
empty stack. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2679 .JUMPDEST,
   pushAt 2680 2 3436,
   opAt 2681 .JUMPI]

/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2679 .JUMPDEST,
   pushAt 2680 2 3436,
   opAt 2681 .JUMPI,
   pushAt 2682 0 0,
   pushAt 2683 0 0,
   opAt 2684 .RETURN]

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
  [opAt 2651 .JUMPDEST,
   pushAt 2652 1 32,
   opAt 2653 .CALLDATALOAD,
   pushAt 2654 2 673,
   opAt 2655 .JUMPI,
   opAt 476 .JUMPDEST]

/-- A zero `esize` with `msize > 32`: the width test `PUSH1 64 CALLDATALOAD PUSH1 32 LT
PUSH2 698 JUMPI` (instructions 8643..8648) leaves for the recogniser too. -/
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2651 .JUMPDEST,
   pushAt 2652 1 32,
   opAt 2653 .CALLDATALOAD,
   pushAt 2654 2 673,
   opAt 2655 .JUMPI,
   pushAt 2656 1 64,
   opAt 2657 .CALLDATALOAD,
   pushAt 2658 1 32,
   opAt 2659 .LT,
   pushAt 2660 2 673,
   opAt 2661 .JUMPI,
   opAt 476 .JUMPDEST]

/-- A zero `esize` with `1 ≤ msize ≤ 32`: the result `1 mod m` is `1 < m`, stored at
word 0 (instructions 8638..8665, pc 3437..4824). -/
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2651 .JUMPDEST,
   pushAt 2652 1 32,
   opAt 2653 .CALLDATALOAD,
   pushAt 2654 2 673,
   opAt 2655 .JUMPI,
   pushAt 2656 1 64,
   opAt 2657 .CALLDATALOAD,
   pushAt 2658 1 32,
   opAt 2659 .LT,
   pushAt 2660 2 673,
   opAt 2661 .JUMPI,
   pushAt 2662 1 64,
   pushAt 2663 2 4749,
   opAt 2664 .JUMP,
   opAt 3647 .JUMPDEST,
   opAt 3648 .CALLDATALOAD,
   pushAt 3649 0 0,
   opAt 3650 .CALLDATALOAD,
   pushAt 3651 1 96,
   opAt 3652 .ADD,
   opAt 3653 .CALLDATALOAD,
   opAt 3654 (.Dup ⟨1,by decide⟩),
   pushAt 3655 1 32,
   opAt 3656 .SUB,
   pushAt 3657 1 3,
   opAt 3658 .SHL,
   opAt 3659 .SHR,
   pushAt 3660 1 1,
   opAt 3661 .LT,
   pushAt 3662 0 0,
   opAt 3663 .MSTORE]

/-- The return of the zero-exponent hit: `DUP1 PUSH1 32 SUB RETURN` returns the low
`msize` bytes of word 0 (instructions 8666..8669). -/
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 3664 (.Dup ⟨0,by decide⟩),
   opAt 3665 .MSIZE,
   opAt 3666 .SUB,
   opAt 3667 .RETURN]



theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3436 = true :=
  CycleSubmission.Global.Binding.jumpDest 2651 (by rfl)

@[simp] theorem packedEmptyPCs (i : Nat) (hi : 2679 ≤ i) (hii : i ≤ 2684) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3481, 3482, 3485, 3486, 3487, 3488] : List Nat)[i - 2679]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem packedHeadPCs (i : Nat) (hi : 2651 ≤ i) (hii : i ≤ 2664) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3436, 3437, 3439, 3440, 3443, 3444, 3446, 3447, 3449, 3450, 3453, 3454, 3456, 3459] : List Nat)[i - 2651]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem packedTailPCs (i : Nat) (hi : 3647 ≤ i) (hii : i ≤ 3667) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([4749, 4750, 4751, 4752, 4753, 4755, 4756, 4757, 4758, 4760, 4761, 4763, 4764, 4765, 4767, 4768, 4769, 4770, 4771, 4772, 4773] : List Nat)[i - 3647]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDestZeroExpTail : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4749 = true :=
  CycleSubmission.Global.Binding.jumpDest 3647 (by rfl)

end CycleSubmission.Global.Fast
