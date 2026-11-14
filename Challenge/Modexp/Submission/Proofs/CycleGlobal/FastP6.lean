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
  [opAt 7841 .JUMPDEST,
   opAt 7842 (.Dup ⟨0,by decide⟩),
   pushAt 7843 2 10867,
   opAt 7844 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7841 .JUMPDEST,
   opAt 7842 (.Dup ⟨0,by decide⟩),
   pushAt 7843 2 10867,
   opAt 7844 .JUMPI,
   pushAt 7845 0 0,
   opAt 7846 .RETURN]
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
  [opAt 7810 .JUMPDEST,
   pushAt 7811 1 32,
   opAt 7812 .CALLDATALOAD,
   pushAt 7813 2 902,
   opAt 7814 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7810 .JUMPDEST,
   pushAt 7811 1 32,
   opAt 7812 .CALLDATALOAD,
   pushAt 7813 2 902,
   opAt 7814 .JUMPI,
   pushAt 7815 1 64,
   opAt 7816 .CALLDATALOAD,
   opAt 7817 (.Dup ⟨0,by decide⟩),
   pushAt 7818 1 32,
   opAt 7819 .LT,
   pushAt 7820 2 10861,
   opAt 7821 .JUMPI,
   opAt 8303 .JUMPDEST,
   opAt 8304 .POP,
   pushAt 8305 2 902,
   opAt 8306 .JUMP,
   opAt 637 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7810 .JUMPDEST,
   pushAt 7811 1 32,
   opAt 7812 .CALLDATALOAD,
   pushAt 7813 2 902,
   opAt 7814 .JUMPI,
   pushAt 7815 1 64,
   opAt 7816 .CALLDATALOAD,
   opAt 7817 (.Dup ⟨0,by decide⟩),
   pushAt 7818 1 32,
   opAt 7819 .LT,
   pushAt 7820 2 10861,
   opAt 7821 .JUMPI,
   pushAt 7822 0 0,
   opAt 7823 .CALLDATALOAD,
   pushAt 7824 1 96,
   opAt 7825 .ADD,
   opAt 7826 .CALLDATALOAD,
   opAt 7827 (.Dup ⟨1,by decide⟩),
   pushAt 7828 1 32,
   opAt 7829 .SUB,
   pushAt 7830 1 3,
   opAt 7831 .SHL,
   opAt 7832 .SHR,
   pushAt 7833 1 1,
   opAt 7834 .LT,
   pushAt 7835 0 0,
   opAt 7836 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7837 (.Dup ⟨0,by decide⟩),
   opAt 7838 .MSIZE,
   opAt 7839 .SUB,
   opAt 7840 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10206 = true :=
  CycleSubmission.Global.Binding.jumpDest 7810 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10861 = true :=
  CycleSubmission.Global.Binding.jumpDest 8303 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7841 ≤ i) (hii : i ≤ 7846) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10248,10249,10250,10253,10254,10255] : List Nat)[i - 7841]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7810 ≤ i) (hii : i ≤ 7840) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10206,10207,10209,10210,10213,10214,10216,10217,10218,10220,10221,10224,10225,10226,10227,10229,10230,10231,10232,10234,10235,10237,10238,10239,10241,10242,10243,10244,10245,10246,10247] : List Nat)[i - 7810]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7822 ≤ i) (hii : i ≤ 7840) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10225,10226,10227,10229,10230,10231,10232,10234,10235,10237,10238,10239,10241,10242,10243,10244,10245,10246,10247] : List Nat)[i - 7822]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8303 ≤ i) (hii : i ≤ 8306) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10861,10862,10863,10866] : List Nat)[i - 8303]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8307 .JUMPDEST,
   pushAt 8308 1 12,
   opAt 8309 .XOR,
   pushAt 8310 2 10206,
   opAt 8311 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8307 .JUMPDEST,
   pushAt 8308 1 12,
   opAt 8309 .XOR,
   pushAt 8310 2 10206,
   opAt 8311 .JUMPI,
   pushAt 8312 0 0,
   opAt 8313 .CALLDATALOAD,
   pushAt 8314 1 32,
   opAt 8315 .CALLDATALOAD,
   opAt 8316 .ADD,
   pushAt 8317 1 96,
   opAt 8318 .ADD,
   opAt 8319 .CALLDATALOAD,
   pushAt 8320 1 160,
   opAt 8321 .SHR,
   pushAt 8322 2 902,
   opAt 8323 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8307 .JUMPDEST,
   pushAt 8308 1 12,
   opAt 8309 .XOR,
   pushAt 8310 2 10206,
   opAt 8311 .JUMPI,
   pushAt 8312 0 0,
   opAt 8313 .CALLDATALOAD,
   pushAt 8314 1 32,
   opAt 8315 .CALLDATALOAD,
   opAt 8316 .ADD,
   pushAt 8317 1 96,
   opAt 8318 .ADD,
   opAt 8319 .CALLDATALOAD,
   pushAt 8320 1 160,
   opAt 8321 .SHR,
   pushAt 8322 2 902,
   opAt 8323 .JUMPI,
   pushAt 8324 1 12,
   pushAt 8325 0 0,
   opAt 8326 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10867 = true :=
  CycleSubmission.Global.Binding.jumpDest 8307 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8307 ≤ i) (hii : i ≤ 8327) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10867,10868,10870,10871,10874,10875,10876,10877,10879,10880,10881,10883,10884,10885,10887,10888,10891,10892,10894,10895,10896] : List Nat)[i - 8307]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
