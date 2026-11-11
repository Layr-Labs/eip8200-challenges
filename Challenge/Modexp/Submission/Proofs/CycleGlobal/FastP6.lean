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
  [opAt 471 (.Dup ⟨4, by decide⟩),
   pushAt 472 1 1,
   pushAt 473 0 0,
   opAt 474 .RETURN]

/-- The empty-modulus test at pc 3482 (instructions 511..513, in the former unreachable
filler behind the memo hit exit) for a nonzero `msize`: `JUMPDEST PUSH2 3437 JUMPI`
consumes `msize` and lands on the zero-exponent test appended at pc 3437 with an
empty stack. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2646 .JUMPDEST,
   pushAt 2647 2 3428,
   opAt 2648 .JUMPI]

/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2646 .JUMPDEST,
   pushAt 2647 2 3428,
   opAt 2648 .JUMPI,
   pushAt 2649 0 0,
   pushAt 2650 0 0,
   opAt 2651 .RETURN]

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
  [opAt 2618 .JUMPDEST,
   pushAt 2619 1 32,
   opAt 2620 .CALLDATALOAD,
   pushAt 2621 2 673,
   opAt 2622 .JUMPI,
   opAt 476 .JUMPDEST]

/-- A zero `esize` with `msize > 32`: the width test `PUSH1 64 CALLDATALOAD PUSH1 32 LT
PUSH2 698 JUMPI` (instructions 8643..8648) leaves for the recogniser too. -/
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2618 .JUMPDEST,
   pushAt 2619 1 32,
   opAt 2620 .CALLDATALOAD,
   pushAt 2621 2 673,
   opAt 2622 .JUMPI,
   pushAt 2623 1 64,
   opAt 2624 .CALLDATALOAD,
   pushAt 2625 1 32,
   opAt 2626 .LT,
   pushAt 2627 2 673,
   opAt 2628 .JUMPI,
   opAt 476 .JUMPDEST]

/-- A zero `esize` with `1 ≤ msize ≤ 32`: the result `1 mod m` is `1 < m`, stored at
word 0 (instructions 8638..8665, pc 3437..4824). -/
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2618 .JUMPDEST,
   pushAt 2619 1 32,
   opAt 2620 .CALLDATALOAD,
   pushAt 2621 2 673,
   opAt 2622 .JUMPI,
   pushAt 2623 1 64,
   opAt 2624 .CALLDATALOAD,
   pushAt 2625 1 32,
   opAt 2626 .LT,
   pushAt 2627 2 673,
   opAt 2628 .JUMPI,
   pushAt 2629 1 64,
   pushAt 2630 2 4717,
   opAt 2631 .JUMP,
   opAt 3618 .JUMPDEST,
   opAt 3619 .CALLDATALOAD,
   pushAt 3620 0 0,
   opAt 3621 .CALLDATALOAD,
   pushAt 3622 1 96,
   opAt 3623 .ADD,
   opAt 3624 .CALLDATALOAD,
   opAt 3625 (.Dup ⟨1, by decide⟩),
   pushAt 3626 1 32,
   opAt 3627 .SUB,
   pushAt 3628 1 3,
   opAt 3629 .SHL,
   opAt 3630 .SHR,
   pushAt 3631 1 1,
   opAt 3632 .LT,
   pushAt 3633 0 0,
   opAt 3634 .MSTORE]

/-- The return of the zero-exponent hit: `DUP1 PUSH1 32 SUB RETURN` returns the low
`msize` bytes of word 0 (instructions 8666..8669). -/
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 3635 (.Dup ⟨0, by decide⟩),
   opAt 3636 .MSIZE,
   opAt 3637 .SUB,
   opAt 3638 .RETURN]



theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3428 = true :=
  CycleSubmission.Global.Binding.jumpDest 2618 (by rfl)

@[simp] theorem packedEmptyPCs (i : Nat) (hi : 2646 ≤ i) (hii : i ≤ 2651) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3473, 3474, 3477, 3478, 3479, 3480] : List Nat)[i - 2646]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem packedHeadPCs (i : Nat) (hi : 2618 ≤ i) (hii : i ≤ 2631) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([3428, 3429, 3431, 3432, 3435, 3436, 3438, 3439, 3441, 3442, 3445, 3446, 3448, 3451] : List Nat)[i - 2618]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem packedTailPCs (i : Nat) (hi : 3618 ≤ i) (hii : i ≤ 3638) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([4717, 4718, 4719, 4720, 4721, 4723, 4724, 4725, 4726, 4728, 4729, 4731, 4732, 4733, 4735, 4736, 4737, 4738, 4739, 4740, 4741] : List Nat)[i - 3618]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDestZeroExpTail : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 4717 = true :=
  CycleSubmission.Global.Binding.jumpDest 3618 (by rfl)

end CycleSubmission.Global.Fast
