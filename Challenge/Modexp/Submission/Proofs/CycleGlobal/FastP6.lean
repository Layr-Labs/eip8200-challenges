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
  [opAt 2681 .JUMPDEST,
   pushAt 2682 2 3457,
   opAt 2683 .JUMPI]

/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2681 .JUMPDEST,
   pushAt 2682 2 3457,
   opAt 2683 .JUMPI,
   pushAt 2684 0 0,
   pushAt 2685 0 0,
   opAt 2686 .RETURN]

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
  [opAt 2653 .JUMPDEST,
   pushAt 2654 1 32,
   opAt 2655 .CALLDATALOAD,
   pushAt 2656 2 673,
   opAt 2657 .JUMPI,
   opAt 476 .JUMPDEST]

/-- A zero `esize` with `msize > 32`: the width test `PUSH1 64 CALLDATALOAD PUSH1 32 LT
PUSH2 698 JUMPI` (instructions 8643..8648) leaves for the recogniser too. -/
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2653 .JUMPDEST,
   pushAt 2654 1 32,
   opAt 2655 .CALLDATALOAD,
   pushAt 2656 2 673,
   opAt 2657 .JUMPI,
   pushAt 2658 1 64,
   opAt 2659 .CALLDATALOAD,
   pushAt 2660 1 32,
   opAt 2661 .LT,
   pushAt 2662 2 673,
   opAt 2663 .JUMPI,
   opAt 476 .JUMPDEST]

/-- A zero `esize` with `1 ≤ msize ≤ 32`: the result `1 mod m` is `1 < m`, stored at
word 0 (instructions 8638..8665, pc 3437..4824). -/
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2653 .JUMPDEST,
   pushAt 2654 1 32,
   opAt 2655 .CALLDATALOAD,
   pushAt 2656 2 673,
   opAt 2657 .JUMPI,
   pushAt 2658 1 64,
   opAt 2659 .CALLDATALOAD,
   pushAt 2660 1 32,
   opAt 2661 .LT,
   pushAt 2662 2 673,
   opAt 2663 .JUMPI,
   pushAt 2664 1 64,
   pushAt 2665 2 4764,
   opAt 2666 .JUMP,
   opAt 3651 .JUMPDEST,
   opAt 3652 .CALLDATALOAD,
   pushAt 3653 0 0,
   opAt 3654 .CALLDATALOAD,
   pushAt 3655 1 96,
   opAt 3656 .ADD,
   opAt 3657 .CALLDATALOAD,
   opAt 3658 (.Dup ⟨1,by decide⟩),
   pushAt 3659 1 32,
   opAt 3660 .SUB,
   pushAt 3661 1 3,
   opAt 3662 .SHL,
   opAt 3663 .SHR,
   pushAt 3664 1 1,
   opAt 3665 .LT,
   pushAt 3666 0 0,
   opAt 3667 .MSTORE]

/-- The return of the zero-exponent hit: `DUP1 PUSH1 32 SUB RETURN` returns the low
`msize` bytes of word 0 (instructions 8666..8669). -/
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 3668 (.Dup ⟨0,by decide⟩),
   opAt 3669 .MSIZE,
   opAt 3670 .SUB,
   opAt 3671 .RETURN]



theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3457 = true :=
  CycleSubmission.Global.Binding.jumpDest 2653 (by rfl)

@[simp] theorem packedEmptyPCs (i : Nat) (hi : 2681 ≤ i) (hii : i ≤ 2686) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3502, 3503, 3506, 3507, 3508, 3509] : List Nat)[i - 2681]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem packedHeadPCs (i : Nat) (hi : 2653 ≤ i) (hii : i ≤ 2666) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3457, 3458, 3460, 3461, 3464, 3465, 3467, 3468, 3470, 3471, 3474, 3475, 3477, 3480] : List Nat)[i - 2653]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem packedTailPCs (i : Nat) (hi : 3651 ≤ i) (hii : i ≤ 3671) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([4764, 4765, 4766, 4767, 4768, 4770, 4771, 4772, 4773, 4775, 4776, 4778, 4779, 4780, 4782, 4783, 4784, 4785, 4786, 4787, 4788] : List Nat)[i - 3651]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDestZeroExpTail : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4764 = true :=
  CycleSubmission.Global.Binding.jumpDest 3651 (by rfl)

end CycleSubmission.Global.Fast
