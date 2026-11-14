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
  [opAt 7423 .JUMPDEST,
   opAt 7424 (.Dup ⟨0,by decide⟩),
   pushAt 7425 2 10761,
   opAt 7426 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7423 .JUMPDEST,
   opAt 7424 (.Dup ⟨0,by decide⟩),
   pushAt 7425 2 10761,
   opAt 7426 .JUMPI,
   pushAt 7427 0 0,
   opAt 7428 .RETURN]
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
  [opAt 7392 .JUMPDEST,
   pushAt 7393 1 32,
   opAt 7394 .CALLDATALOAD,
   pushAt 7395 2 911,
   opAt 7396 .JUMPI,
   opAt 645 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7392 .JUMPDEST,
   pushAt 7393 1 32,
   opAt 7394 .CALLDATALOAD,
   pushAt 7395 2 911,
   opAt 7396 .JUMPI,
   pushAt 7397 1 64,
   opAt 7398 .CALLDATALOAD,
   opAt 7399 (.Dup ⟨0,by decide⟩),
   pushAt 7400 1 32,
   opAt 7401 .LT,
   pushAt 7402 2 10755,
   opAt 7403 .JUMPI,
   opAt 8397 .JUMPDEST,
   opAt 8398 .POP,
   pushAt 8399 2 911,
   opAt 8400 .JUMP,
   opAt 645 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7392 .JUMPDEST,
   pushAt 7393 1 32,
   opAt 7394 .CALLDATALOAD,
   pushAt 7395 2 911,
   opAt 7396 .JUMPI,
   pushAt 7397 1 64,
   opAt 7398 .CALLDATALOAD,
   opAt 7399 (.Dup ⟨0,by decide⟩),
   pushAt 7400 1 32,
   opAt 7401 .LT,
   pushAt 7402 2 10755,
   opAt 7403 .JUMPI,
   pushAt 7404 0 0,
   opAt 7405 .CALLDATALOAD,
   pushAt 7406 1 96,
   opAt 7407 .ADD,
   opAt 7408 .CALLDATALOAD,
   opAt 7409 (.Dup ⟨1,by decide⟩),
   pushAt 7410 1 32,
   opAt 7411 .SUB,
   pushAt 7412 1 3,
   opAt 7413 .SHL,
   opAt 7414 .SHR,
   pushAt 7415 1 1,
   opAt 7416 .LT,
   pushAt 7417 0 0,
   opAt 7418 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7419 (.Dup ⟨0,by decide⟩),
   opAt 7420 .MSIZE,
   opAt 7421 .SUB,
   opAt 7422 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 9518 = true :=
  CycleSubmission.Global.Binding.jumpDest 7392 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10755 = true :=
  CycleSubmission.Global.Binding.jumpDest 8397 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7423 ≤ i) (hii : i ≤ 7428) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([9560,9561,9562,9565,9566,9567] : List Nat)[i - 7423]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7392 ≤ i) (hii : i ≤ 7422) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([9518,9519,9521,9522,9525,9526,9528,9529,9530,9532,9533,9536,9537,9538,9539,9541,9542,9543,9544,9546,9547,9549,9550,9551,9553,9554,9555,9556,9557,9558,9559] : List Nat)[i - 7392]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7404 ≤ i) (hii : i ≤ 7422) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([9537,9538,9539,9541,9542,9543,9544,9546,9547,9549,9550,9551,9553,9554,9555,9556,9557,9558,9559] : List Nat)[i - 7404]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8397 ≤ i) (hii : i ≤ 8400) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10755,10756,10757,10760] : List Nat)[i - 8397]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8401 .JUMPDEST,
   pushAt 8402 1 12,
   opAt 8403 .XOR,
   pushAt 8404 2 9518,
   opAt 8405 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8401 .JUMPDEST,
   pushAt 8402 1 12,
   opAt 8403 .XOR,
   pushAt 8404 2 9518,
   opAt 8405 .JUMPI,
   pushAt 8406 0 0,
   opAt 8407 .CALLDATALOAD,
   pushAt 8408 1 32,
   opAt 8409 .CALLDATALOAD,
   opAt 8410 .ADD,
   pushAt 8411 1 96,
   opAt 8412 .ADD,
   opAt 8413 .CALLDATALOAD,
   pushAt 8414 1 160,
   opAt 8415 .SHR,
   pushAt 8416 2 911,
   opAt 8417 .JUMPI,
   opAt 645 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8401 .JUMPDEST,
   pushAt 8402 1 12,
   opAt 8403 .XOR,
   pushAt 8404 2 9518,
   opAt 8405 .JUMPI,
   pushAt 8406 0 0,
   opAt 8407 .CALLDATALOAD,
   pushAt 8408 1 32,
   opAt 8409 .CALLDATALOAD,
   opAt 8410 .ADD,
   pushAt 8411 1 96,
   opAt 8412 .ADD,
   opAt 8413 .CALLDATALOAD,
   pushAt 8414 1 160,
   opAt 8415 .SHR,
   pushAt 8416 2 911,
   opAt 8417 .JUMPI,
   pushAt 8418 1 12,
   pushAt 8419 0 0,
   opAt 8420 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10761 = true :=
  CycleSubmission.Global.Binding.jumpDest 8401 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8401 ≤ i) (hii : i ≤ 8421) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10761,10762,10764,10765,10768,10769,10770,10771,10773,10774,10775,10777,10778,10779,10781,10782,10785,10786,10788,10789,10790] : List Nat)[i - 8401]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
