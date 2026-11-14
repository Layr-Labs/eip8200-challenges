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
  [opAt 7917 .JUMPDEST,
   opAt 7918 (.Dup ⟨0,by decide⟩),
   pushAt 7919 2 10757,
   opAt 7920 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7917 .JUMPDEST,
   opAt 7918 (.Dup ⟨0,by decide⟩),
   pushAt 7919 2 10757,
   opAt 7920 .JUMPI,
   pushAt 7921 0 0,
   opAt 7922 .RETURN]
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
  [opAt 7886 .JUMPDEST,
   pushAt 7887 1 32,
   opAt 7888 .CALLDATALOAD,
   pushAt 7889 2 911,
   opAt 7890 .JUMPI,
   opAt 645 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7886 .JUMPDEST,
   pushAt 7887 1 32,
   opAt 7888 .CALLDATALOAD,
   pushAt 7889 2 911,
   opAt 7890 .JUMPI,
   pushAt 7891 1 64,
   opAt 7892 .CALLDATALOAD,
   opAt 7893 (.Dup ⟨0,by decide⟩),
   pushAt 7894 1 32,
   opAt 7895 .LT,
   pushAt 7896 2 10751,
   opAt 7897 .JUMPI,
   opAt 8397 .JUMPDEST,
   opAt 8398 .POP,
   pushAt 8399 2 911,
   opAt 8400 .JUMP,
   opAt 645 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7886 .JUMPDEST,
   pushAt 7887 1 32,
   opAt 7888 .CALLDATALOAD,
   pushAt 7889 2 911,
   opAt 7890 .JUMPI,
   pushAt 7891 1 64,
   opAt 7892 .CALLDATALOAD,
   opAt 7893 (.Dup ⟨0,by decide⟩),
   pushAt 7894 1 32,
   opAt 7895 .LT,
   pushAt 7896 2 10751,
   opAt 7897 .JUMPI,
   pushAt 7898 0 0,
   opAt 7899 .CALLDATALOAD,
   pushAt 7900 1 96,
   opAt 7901 .ADD,
   opAt 7902 .CALLDATALOAD,
   opAt 7903 (.Dup ⟨1,by decide⟩),
   pushAt 7904 1 32,
   opAt 7905 .SUB,
   pushAt 7906 1 3,
   opAt 7907 .SHL,
   opAt 7908 .SHR,
   pushAt 7909 1 1,
   opAt 7910 .LT,
   pushAt 7911 0 0,
   opAt 7912 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7913 (.Dup ⟨0,by decide⟩),
   opAt 7914 .MSIZE,
   opAt 7915 .SUB,
   opAt 7916 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10076 = true :=
  CycleSubmission.Global.Binding.jumpDest 7886 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10751 = true :=
  CycleSubmission.Global.Binding.jumpDest 8397 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7917 ≤ i) (hii : i ≤ 7922) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10118,10119,10120,10123,10124,10125] : List Nat)[i - 7917]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7886 ≤ i) (hii : i ≤ 7916) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10076,10077,10079,10080,10083,10084,10086,10087,10088,10090,10091,10094,10095,10096,10097,10099,10100,10101,10102,10104,10105,10107,10108,10109,10111,10112,10113,10114,10115,10116,10117] : List Nat)[i - 7886]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7898 ≤ i) (hii : i ≤ 7916) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10095,10096,10097,10099,10100,10101,10102,10104,10105,10107,10108,10109,10111,10112,10113,10114,10115,10116,10117] : List Nat)[i - 7898]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8397 ≤ i) (hii : i ≤ 8400) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10751,10752,10753,10756] : List Nat)[i - 8397]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8401 .JUMPDEST,
   pushAt 8402 1 12,
   opAt 8403 .XOR,
   pushAt 8404 2 10076,
   opAt 8405 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8401 .JUMPDEST,
   pushAt 8402 1 12,
   opAt 8403 .XOR,
   pushAt 8404 2 10076,
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
   pushAt 8404 2 10076,
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
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10757 = true :=
  CycleSubmission.Global.Binding.jumpDest 8401 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8401 ≤ i) (hii : i ≤ 8421) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10757,10758,10760,10761,10764,10765,10766,10767,10769,10770,10771,10773,10774,10775,10777,10778,10781,10782,10784,10785,10786] : List Nat)[i - 8401]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
