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
  [opAt 479 (.Dup ⟨4, by decide⟩),
   pushAt 480 1 1,
   pushAt 481 0 0,
   opAt 482 .RETURN]

/-- The empty-modulus test at pc 3482 (instructions 511..513, in the former unreachable
filler behind the memo hit exit) for a nonzero `msize`: `JUMPDEST PUSH2 3437 JUMPI`
consumes `msize` and lands on the zero-exponent test appended at pc 3437 with an
empty stack. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2668 .JUMPDEST,
   pushAt 2669 2 3437,
   opAt 2670 .JUMPI]

/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2668 .JUMPDEST,
   pushAt 2669 2 3437,
   opAt 2670 .JUMPI,
   pushAt 2671 0 0,
   pushAt 2672 0 0,
   opAt 2673 .RETURN]

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
  [opAt 2640 .JUMPDEST,
   pushAt 2641 1 32,
   opAt 2642 .CALLDATALOAD,
   pushAt 2643 2 698,
   opAt 2644 .JUMPI,
   opAt 484 .JUMPDEST]

/-- A zero `esize` with `msize > 32`: the width test `PUSH1 64 CALLDATALOAD PUSH1 32 LT
PUSH2 698 JUMPI` (instructions 8643..8648) leaves for the recogniser too. -/
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2640 .JUMPDEST,
   pushAt 2641 1 32,
   opAt 2642 .CALLDATALOAD,
   pushAt 2643 2 698,
   opAt 2644 .JUMPI,
   pushAt 2645 1 64,
   opAt 2646 .CALLDATALOAD,
   pushAt 2647 1 32,
   opAt 2648 .LT,
   pushAt 2649 2 698,
   opAt 2650 .JUMPI,
   opAt 484 .JUMPDEST]

/-- A zero `esize` with `1 ≤ msize ≤ 32`: the result `1 mod m` is `1 < m`, stored at
word 0 (instructions 8638..8665, pc 3437..4824). -/
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2640 .JUMPDEST,
   pushAt 2641 1 32,
   opAt 2642 .CALLDATALOAD,
   pushAt 2643 2 698,
   opAt 2644 .JUMPI,
   pushAt 2645 1 64,
   opAt 2646 .CALLDATALOAD,
   pushAt 2647 1 32,
   opAt 2648 .LT,
   pushAt 2649 2 698,
   opAt 2650 .JUMPI,
   pushAt 2651 1 64,
   pushAt 2652 2 4804,
   opAt 2653 .JUMP,
   opAt 3665 .JUMPDEST,
   opAt 3666 .CALLDATALOAD,
   pushAt 3667 0 0,
   opAt 3668 .CALLDATALOAD,
   pushAt 3669 1 96,
   opAt 3670 .ADD,
   opAt 3671 .CALLDATALOAD,
   opAt 3672 (.Dup ⟨1, by decide⟩),
   pushAt 3673 1 32,
   opAt 3674 .SUB,
   pushAt 3675 1 3,
   opAt 3676 .SHL,
   opAt 3677 .SHR,
   pushAt 3678 1 1,
   opAt 3679 .LT,
   pushAt 3680 0 0,
   opAt 3681 .MSTORE]

/-- The return of the zero-exponent hit: `DUP1 PUSH1 32 SUB RETURN` returns the low
`msize` bytes of word 0 (instructions 8666..8669). -/
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 3682 (.Dup ⟨0, by decide⟩),
   pushAt 3683 1 32,
   opAt 3684 .SUB,
   opAt 3685 .RETURN]



theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3437 = true :=
  CycleSubmission.Global.Binding.jumpDest 2640 (by rfl)

@[simp] theorem packedEmptyPCs (i : Nat) (hi : 2668 ≤ i) (hii : i ≤ 2673) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3482, 3483, 3486, 3487, 3488, 3489] : List Nat)[i - 2668]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem packedHeadPCs (i : Nat) (hi : 2640 ≤ i) (hii : i ≤ 2653) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3437, 3438, 3440, 3441, 3444, 3445, 3447, 3448, 3450, 3451, 3454, 3455, 3457, 3460] : List Nat)[i - 2640]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem packedTailPCs (i : Nat) (hi : 3665 ≤ i) (hii : i ≤ 3685) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([4804, 4805, 4806, 4807, 4808, 4810, 4811, 4812, 4813, 4815, 4816, 4818, 4819, 4820, 4822, 4823, 4824, 4825, 4826, 4828, 4829] : List Nat)[i - 3665]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDestZeroExpTail : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4804 = true :=
  CycleSubmission.Global.Binding.jumpDest 3665 (by rfl)

end CycleSubmission.Global.Fast
