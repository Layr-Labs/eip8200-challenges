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
  [opAt 483 (.Dup ⟨4, by decide⟩),
   pushAt 484 1 1,
   pushAt 485 0 0,
   opAt 486 .RETURN]

/-- The empty-modulus test at pc 737 (instructions 511..513, in the former unreachable
filler behind the memo hit exit) for a nonzero `msize`: `JUMPDEST PUSH2 10983 JUMPI`
consumes `msize` and lands on the zero-exponent test appended at pc 10983 with an
empty stack. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 511 .JUMPDEST,
   pushAt 512 2 10983,
   opAt 513 .JUMPI]

/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 742..744), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 511 .JUMPDEST,
   pushAt 512 2 10983,
   opAt 513 .JUMPI,
   pushAt 514 0 0,
   pushAt 515 0 0,
   opAt 516 .RETURN]

/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/

/-- The zero-exponent test appended at pc 10983 (instructions 8638..8642) for a nonzero
`esize`: `JUMPDEST PUSH1 32 CALLDATALOAD PUSH2 698 JUMPI` lands on the `JUMPDEST` at
pc 698 (instruction 488), which falls into the fixed-vector recogniser at pc 699 with an
empty stack. -/
def blkZeroExpMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8620 .JUMPDEST,
   pushAt 8621 1 32,
   opAt 8622 .CALLDATALOAD,
   pushAt 8623 2 698,
   opAt 8624 .JUMPI,
   opAt 488 .JUMPDEST]

/-- A zero `esize` with `msize > 32`: the width test `PUSH1 64 CALLDATALOAD PUSH1 32 LT
PUSH2 698 JUMPI` (instructions 8643..8648) leaves for the recogniser too. -/
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8620 .JUMPDEST,
   pushAt 8621 1 32,
   opAt 8622 .CALLDATALOAD,
   pushAt 8623 2 698,
   opAt 8624 .JUMPI,
   pushAt 8625 1 64,
   opAt 8626 .CALLDATALOAD,
   pushAt 8627 1 32,
   opAt 8628 .LT,
   pushAt 8629 2 698,
   opAt 8630 .JUMPI,
   opAt 488 .JUMPDEST]

/-- A zero `esize` with `1 ≤ msize ≤ 32`: the result `1 mod m` is `1 < m`, stored at
word 0 (instructions 8638..8665, pc 10983..11022). -/
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8620 .JUMPDEST,
   pushAt 8621 1 32,
   opAt 8622 .CALLDATALOAD,
   pushAt 8623 2 698,
   opAt 8624 .JUMPI,
   pushAt 8625 1 64,
   opAt 8626 .CALLDATALOAD,
   pushAt 8627 1 32,
   opAt 8628 .LT,
   pushAt 8629 2 698,
   opAt 8630 .JUMPI,
   pushAt 8631 1 64,
   opAt 8632 .CALLDATALOAD,
   pushAt 8633 0 0,
   opAt 8634 .CALLDATALOAD,
   pushAt 8635 1 96,
   opAt 8636 .ADD,
   opAt 8637 .CALLDATALOAD,
   opAt 8638 (.Dup ⟨1, by decide⟩),
   pushAt 8639 1 32,
   opAt 8640 .SUB,
   pushAt 8641 1 3,
   opAt 8642 .SHL,
   opAt 8643 .SHR,
   pushAt 8644 1 1,
   opAt 8645 .LT,
   pushAt 8646 0 0,
   opAt 8647 .MSTORE]

/-- The return of the zero-exponent hit: `DUP1 PUSH1 32 SUB RETURN` returns the low
`msize` bytes of word 0 (instructions 8666..8669). -/
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8648 (.Dup ⟨0, by decide⟩),
   pushAt 8649 1 32,
   opAt 8650 .SUB,
   opAt 8651 .RETURN]

@[simp] theorem zeroExpPCs (i : Nat) (hi : 8620 ≤ i) (hii : i ≤ 8651) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      [10983, 10984, 10986, 10987, 10990, 10991, 10993, 10994, 10996, 10997, 11000,
       11001, 11003, 11004, 11005, 11006, 11008, 11009, 11010, 11011, 11013, 11014,
       11016, 11017, 11018, 11020, 11021, 11022, 11023, 11024, 11026, 11027][i - 8620]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

theorem jumpDestZeroExp :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10983 = true :=
  CycleSubmission.Global.Binding.jumpDest 8620 (by rfl)

end CycleSubmission.Global.Fast
