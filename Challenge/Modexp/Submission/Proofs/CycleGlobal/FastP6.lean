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
  [opAt 640 (.Dup ⟨4,by decide⟩),
   pushAt 641 1 1,
   pushAt 642 0 0,
   opAt 643 .RETURN]

/-- The empty-modulus test at pc 3482 (instructions 511..513, in the former unreachable
filler behind the memo hit exit) for a nonzero `msize`: `JUMPDEST PUSH2 3437 JUMPI`
consumes `msize` and lands on the zero-exponent test appended at pc 3437 with an
empty stack. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7422 .JUMPDEST,
   opAt 7423 (.Dup ⟨0,by decide⟩),
   pushAt 7424 2 10733,
   opAt 7425 .JUMPI]


/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7422 .JUMPDEST,
   opAt 7423 (.Dup ⟨0,by decide⟩),
   pushAt 7424 2 10733,
   opAt 7425 .JUMPI,
   pushAt 7426 0 0,
   opAt 7427 .RETURN]


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
  [opAt 7391 .JUMPDEST,
   pushAt 7392 1 32,
   opAt 7393 .CALLDATALOAD,
   pushAt 7394 2 911,
   opAt 7395 .JUMPI,
   opAt 645 .JUMPDEST]

def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7391 .JUMPDEST,
   pushAt 7392 1 32,
   opAt 7393 .CALLDATALOAD,
   pushAt 7394 2 911,
   opAt 7395 .JUMPI,
   pushAt 7396 1 64,
   opAt 7397 .CALLDATALOAD,
   opAt 7398 (.Dup ⟨0,by decide⟩),
   pushAt 7399 1 32,
   opAt 7400 .LT,
   pushAt 7401 2 10727,
   opAt 7402 .JUMPI,
   opAt 8395 .JUMPDEST,
   opAt 8396 .POP,
   pushAt 8397 2 911,
   opAt 8398 .JUMP,
   opAt 645 .JUMPDEST]

def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7391 .JUMPDEST,
   pushAt 7392 1 32,
   opAt 7393 .CALLDATALOAD,
   pushAt 7394 2 911,
   opAt 7395 .JUMPI,
   pushAt 7396 1 64,
   opAt 7397 .CALLDATALOAD,
   opAt 7398 (.Dup ⟨0,by decide⟩),
   pushAt 7399 1 32,
   opAt 7400 .LT,
   pushAt 7401 2 10727,
   opAt 7402 .JUMPI,
   pushAt 7403 0 0,
   opAt 7404 .CALLDATALOAD,
   pushAt 7405 1 96,
   opAt 7406 .ADD,
   opAt 7407 .CALLDATALOAD,
   opAt 7408 (.Dup ⟨1,by decide⟩),
   pushAt 7409 1 32,
   opAt 7410 .SUB,
   pushAt 7411 1 3,
   opAt 7412 .SHL,
   opAt 7413 .SHR,
   pushAt 7414 1 1,
   opAt 7415 .LT,
   pushAt 7416 0 0,
   opAt 7417 .MSTORE]

def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7418 (.Dup ⟨0,by decide⟩),
   opAt 7419 .MSIZE,
   opAt 7420 .SUB,
   opAt 7421 .RETURN]

theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 9490 = true :=
  CycleSubmission.Global.Binding.jumpDest 7391 (by rfl)

theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10727 = true :=
  CycleSubmission.Global.Binding.jumpDest 8395 (by rfl)

@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7422 ≤ i) (hii : i ≤ 7427) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([9532,9533,9534,9537,9538,9539] : List Nat)[i - 7422]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem packedHeadPCs (i : Nat) (hi : 7391 ≤ i) (hii : i ≤ 7421) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([9490,9491,9493,9494,9497,9498,9500,9501,9502,9504,9505,9508,9509,9510,9511,9513,9514,9515,9516,9518,9519,9521,9522,9523,9525,9526,9527,9528,9529,9530,9531] : List Nat)[i - 7391]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem packedTailPCs (i : Nat) (hi : 7403 ≤ i) (hii : i ≤ 7421) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([9509,9510,9511,9513,9514,9515,9516,9518,9519,9521,9522,9523,9525,9526,9527,9528,9529,9530,9531] : List Nat)[i - 7403]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8395 ≤ i) (hii : i ≤ 8398) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10727,10728,10729,10732] : List Nat)[i - 8395]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl


def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8399 .JUMPDEST,
   pushAt 8400 1 12,
   opAt 8401 .XOR,
   pushAt 8402 2 9490,
   opAt 8403 .JUMPI]

def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8399 .JUMPDEST,
   pushAt 8400 1 12,
   opAt 8401 .XOR,
   pushAt 8402 2 9490,
   opAt 8403 .JUMPI,
   pushAt 8404 0 0,
   opAt 8405 .CALLDATALOAD,
   pushAt 8406 1 32,
   opAt 8407 .CALLDATALOAD,
   opAt 8408 .ADD,
   pushAt 8409 1 96,
   opAt 8410 .ADD,
   opAt 8411 .CALLDATALOAD,
   pushAt 8412 1 160,
   opAt 8413 .SHR,
   pushAt 8414 2 911,
   opAt 8415 .JUMPI,
   opAt 645 .JUMPDEST]

def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8399 .JUMPDEST,
   pushAt 8400 1 12,
   opAt 8401 .XOR,
   pushAt 8402 2 9490,
   opAt 8403 .JUMPI,
   pushAt 8404 0 0,
   opAt 8405 .CALLDATALOAD,
   pushAt 8406 1 32,
   opAt 8407 .CALLDATALOAD,
   opAt 8408 .ADD,
   pushAt 8409 1 96,
   opAt 8410 .ADD,
   opAt 8411 .CALLDATALOAD,
   pushAt 8412 1 160,
   opAt 8413 .SHR,
   pushAt 8414 2 911,
   opAt 8415 .JUMPI,
   pushAt 8416 1 12,
   pushAt 8417 0 0,
   opAt 8418 .RETURN]

theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10733 = true :=
  CycleSubmission.Global.Binding.jumpDest 8399 (by rfl)

@[simp] theorem packedZero12PCs (i : Nat) (hi : 8399 ≤ i) (hii : i ≤ 8419) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10733,10734,10736,10737,10740,10741,10742,10743,10745,10746,10747,10749,10750,10751,10753,10754,10757,10758,10760,10761,10762] : List Nat)[i - 8399]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl

end CycleSubmission.Global.Fast
