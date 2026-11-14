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
  []
/-- The empty-modulus test at pc 3482 (instructions 511..513, in the former unreachable
filler behind the memo hit exit) for a nonzero `msize`: `JUMPDEST PUSH2 3437 JUMPI`
consumes `msize` and lands on the zero-exponent test appended at pc 3437 with an
empty stack. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7837 .JUMPDEST,
   opAt 7838 (.Dup ⟨0,by decide⟩),
   pushAt 7839 2 10851,
   opAt 7840 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7837 .JUMPDEST,
   opAt 7838 (.Dup ⟨0,by decide⟩),
   pushAt 7839 2 10851,
   opAt 7840 .JUMPI,
   pushAt 7841 0 0,
   opAt 7842 .RETURN]
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
  [opAt 7806 .JUMPDEST,
   pushAt 7807 1 32,
   opAt 7808 .CALLDATALOAD,
   pushAt 7809 2 902,
   opAt 7810 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7806 .JUMPDEST,
   pushAt 7807 1 32,
   opAt 7808 .CALLDATALOAD,
   pushAt 7809 2 902,
   opAt 7810 .JUMPI,
   pushAt 7811 1 64,
   opAt 7812 .CALLDATALOAD,
   opAt 7813 (.Dup ⟨0,by decide⟩),
   pushAt 7814 1 32,
   opAt 7815 .LT,
   pushAt 7816 2 10845,
   opAt 7817 .JUMPI,
   opAt 8299 .JUMPDEST,
   opAt 8300 .POP,
   pushAt 8301 2 902,
   opAt 8302 .JUMP,
   opAt 637 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7806 .JUMPDEST,
   pushAt 7807 1 32,
   opAt 7808 .CALLDATALOAD,
   pushAt 7809 2 902,
   opAt 7810 .JUMPI,
   pushAt 7811 1 64,
   opAt 7812 .CALLDATALOAD,
   opAt 7813 (.Dup ⟨0,by decide⟩),
   pushAt 7814 1 32,
   opAt 7815 .LT,
   pushAt 7816 2 10845,
   opAt 7817 .JUMPI,
   pushAt 7818 0 0,
   opAt 7819 .CALLDATALOAD,
   pushAt 7820 1 96,
   opAt 7821 .ADD,
   opAt 7822 .CALLDATALOAD,
   opAt 7823 (.Dup ⟨1,by decide⟩),
   pushAt 7824 1 32,
   opAt 7825 .SUB,
   pushAt 7826 1 3,
   opAt 7827 .SHL,
   opAt 7828 .SHR,
   pushAt 7829 1 1,
   opAt 7830 .LT,
   pushAt 7831 0 0,
   opAt 7832 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7833 (.Dup ⟨0,by decide⟩),
   opAt 7834 .MSIZE,
   opAt 7835 .SUB,
   opAt 7836 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10190 = true :=
  CycleSubmission.Global.Binding.jumpDest 7806 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10845 = true :=
  CycleSubmission.Global.Binding.jumpDest 8299 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7837 ≤ i) (hii : i ≤ 7842) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10232,10233,10234,10237,10238,10239] : List Nat)[i - 7837]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7806 ≤ i) (hii : i ≤ 7836) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10190,10191,10193,10194,10197,10198,10200,10201,10202,10204,10205,10208,10209,10210,10211,10213,10214,10215,10216,10218,10219,10221,10222,10223,10225,10226,10227,10228,10229,10230,10231] : List Nat)[i - 7806]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7818 ≤ i) (hii : i ≤ 7836) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10209,10210,10211,10213,10214,10215,10216,10218,10219,10221,10222,10223,10225,10226,10227,10228,10229,10230,10231] : List Nat)[i - 7818]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8299 ≤ i) (hii : i ≤ 8302) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10845,10846,10847,10850] : List Nat)[i - 8299]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8303 .JUMPDEST,
   pushAt 8304 1 12,
   opAt 8305 .XOR,
   pushAt 8306 2 10190,
   opAt 8307 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8303 .JUMPDEST,
   pushAt 8304 1 12,
   opAt 8305 .XOR,
   pushAt 8306 2 10190,
   opAt 8307 .JUMPI,
   pushAt 8308 0 0,
   opAt 8309 .CALLDATALOAD,
   pushAt 8310 1 32,
   opAt 8311 .CALLDATALOAD,
   opAt 8312 .ADD,
   pushAt 8313 1 96,
   opAt 8314 .ADD,
   opAt 8315 .CALLDATALOAD,
   pushAt 8316 1 160,
   opAt 8317 .SHR,
   pushAt 8318 2 902,
   opAt 8319 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8303 .JUMPDEST,
   pushAt 8304 1 12,
   opAt 8305 .XOR,
   pushAt 8306 2 10190,
   opAt 8307 .JUMPI,
   pushAt 8308 0 0,
   opAt 8309 .CALLDATALOAD,
   pushAt 8310 1 32,
   opAt 8311 .CALLDATALOAD,
   opAt 8312 .ADD,
   pushAt 8313 1 96,
   opAt 8314 .ADD,
   opAt 8315 .CALLDATALOAD,
   pushAt 8316 1 160,
   opAt 8317 .SHR,
   pushAt 8318 2 902,
   opAt 8319 .JUMPI,
   pushAt 8320 1 12,
   pushAt 8321 0 0,
   opAt 8322 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10851 = true :=
  CycleSubmission.Global.Binding.jumpDest 8303 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8303 ≤ i) (hii : i ≤ 8323) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10851,10852,10854,10855,10858,10859,10860,10861,10863,10864,10865,10867,10868,10869,10871,10872,10875,10876,10878,10879,10880] : List Nat)[i - 8303]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
