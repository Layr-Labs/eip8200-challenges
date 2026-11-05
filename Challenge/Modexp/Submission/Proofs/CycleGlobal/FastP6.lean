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
  [opAt 2735 .JUMPDEST,
   pushAt 2736 2 3595,
   opAt 2737 .JUMPI]

/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2735 .JUMPDEST,
   pushAt 2736 2 3595,
   opAt 2737 .JUMPI,
   pushAt 2738 0 0,
   pushAt 2739 0 0,
   opAt 2740 .RETURN]

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
  [opAt 2707 .JUMPDEST,
   pushAt 2708 1 32,
   opAt 2709 .CALLDATALOAD,
   pushAt 2710 2 698,
   opAt 2711 .JUMPI,
   opAt 484 .JUMPDEST]

/-- A zero `esize` with `msize > 32`: the width test `PUSH1 64 CALLDATALOAD PUSH1 32 LT
PUSH2 698 JUMPI` (instructions 8643..8648) leaves for the recogniser too. -/
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2707 .JUMPDEST,
   pushAt 2708 1 32,
   opAt 2709 .CALLDATALOAD,
   pushAt 2710 2 698,
   opAt 2711 .JUMPI,
   pushAt 2712 1 64,
   opAt 2713 .CALLDATALOAD,
   pushAt 2714 1 32,
   opAt 2715 .LT,
   pushAt 2716 2 698,
   opAt 2717 .JUMPI,
   opAt 484 .JUMPDEST]

/-- A zero `esize` with `1 ≤ msize ≤ 32`: the result `1 mod m` is `1 < m`, stored at
word 0 (instructions 8638..8665, pc 3437..4824). -/
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2707 .JUMPDEST,
   pushAt 2708 1 32,
   opAt 2709 .CALLDATALOAD,
   pushAt 2710 2 698,
   opAt 2711 .JUMPI,
   pushAt 2712 1 64,
   opAt 2713 .CALLDATALOAD,
   pushAt 2714 1 32,
   opAt 2715 .LT,
   pushAt 2716 2 698,
   opAt 2717 .JUMPI,
   pushAt 2718 1 64,
   pushAt 2719 2 4918,
   opAt 2720 .JUMP,
   opAt 3732 .JUMPDEST,
   opAt 3733 .CALLDATALOAD,
   pushAt 3734 0 0,
   opAt 3735 .CALLDATALOAD,
   pushAt 3736 1 96,
   opAt 3737 .ADD,
   opAt 3738 .CALLDATALOAD,
   opAt 3739 (.Dup ⟨1, by decide⟩),
   pushAt 3740 1 32,
   opAt 3741 .SUB,
   pushAt 3742 2 3,
   opAt 3743 .SHL,
   opAt 3744 .SHR,
   pushAt 3745 1 1,
   opAt 3746 .LT,
   pushAt 3747 0 0,
   opAt 3748 .MSTORE]

/-- The return of the zero-exponent hit: `DUP1 PUSH1 32 SUB RETURN` returns the low
`msize` bytes of word 0 (instructions 8666..8669). -/
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 3749 (.Dup ⟨0, by decide⟩),
   opAt 3750 .MSIZE,
   opAt 3751 .SUB,
   opAt 3752 .RETURN]



theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3595 = true :=
  CycleSubmission.Global.Binding.jumpDest 2707 (by rfl)

@[simp] theorem packedEmptyPCs (i : Nat) (hi : 2735 ≤ i) (hii : i ≤ 2740) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3640, 3641, 3644, 3645, 3646, 3647] : List Nat)[i - 2735]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem packedHeadPCs (i : Nat) (hi : 2707 ≤ i) (hii : i ≤ 2720) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3595, 3596, 3598, 3599, 3602, 3603, 3605, 3606, 3608, 3609, 3612, 3613, 3615, 3618] : List Nat)[i - 2707]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem packedTailPCs (i : Nat) (hi : 3732 ≤ i) (hii : i ≤ 3752) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([4918, 4919, 4920, 4921, 4922, 4924, 4925, 4926, 4927, 4929, 4930, 4933, 4934, 4935, 4937, 4938, 4939, 4940, 4941, 4942, 4943] : List Nat)[i - 3732]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDestZeroExpTail : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4918 = true :=
  CycleSubmission.Global.Binding.jumpDest 3732 (by rfl)

end CycleSubmission.Global.Fast
