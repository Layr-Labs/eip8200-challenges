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
  [opAt 7829 .JUMPDEST,
   opAt 7830 (.Dup ⟨0,by decide⟩),
   pushAt 7831 2 10964,
   opAt 7832 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7829 .JUMPDEST,
   opAt 7830 (.Dup ⟨0,by decide⟩),
   pushAt 7831 2 10964,
   opAt 7832 .JUMPI,
   pushAt 7833 0 0,
   opAt 7834 .RETURN]
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
  [opAt 7798 .JUMPDEST,
   pushAt 7799 1 32,
   opAt 7800 .CALLDATALOAD,
   pushAt 7801 2 902,
   opAt 7802 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7798 .JUMPDEST,
   pushAt 7799 1 32,
   opAt 7800 .CALLDATALOAD,
   pushAt 7801 2 902,
   opAt 7802 .JUMPI,
   pushAt 7803 1 64,
   opAt 7804 .CALLDATALOAD,
   opAt 7805 (.Dup ⟨0,by decide⟩),
   pushAt 7806 1 32,
   opAt 7807 .LT,
   pushAt 7808 2 10958,
   opAt 7809 .JUMPI,
   opAt 8288 .JUMPDEST,
   opAt 8289 .POP,
   pushAt 8290 2 902,
   opAt 8291 .JUMP,
   opAt 637 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7798 .JUMPDEST,
   pushAt 7799 1 32,
   opAt 7800 .CALLDATALOAD,
   pushAt 7801 2 902,
   opAt 7802 .JUMPI,
   pushAt 7803 1 64,
   opAt 7804 .CALLDATALOAD,
   opAt 7805 (.Dup ⟨0,by decide⟩),
   pushAt 7806 1 32,
   opAt 7807 .LT,
   pushAt 7808 2 10958,
   opAt 7809 .JUMPI,
   pushAt 7810 0 0,
   opAt 7811 .CALLDATALOAD,
   pushAt 7812 1 96,
   opAt 7813 .ADD,
   opAt 7814 .CALLDATALOAD,
   opAt 7815 (.Dup ⟨1,by decide⟩),
   pushAt 7816 1 32,
   opAt 7817 .SUB,
   pushAt 7818 1 3,
   opAt 7819 .SHL,
   opAt 7820 .SHR,
   pushAt 7821 1 1,
   opAt 7822 .LT,
   pushAt 7823 0 0,
   opAt 7824 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7825 (.Dup ⟨0,by decide⟩),
   opAt 7826 .MSIZE,
   opAt 7827 .SUB,
   opAt 7828 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10274 = true :=
  CycleSubmission.Global.Binding.jumpDest 7798 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10958 = true :=
  CycleSubmission.Global.Binding.jumpDest 8288 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7829 ≤ i) (hii : i ≤ 7834) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10316,10317,10318,10321,10322,10323] : List Nat)[i - 7829]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7798 ≤ i) (hii : i ≤ 7828) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10274,10275,10277,10278,10281,10282,10284,10285,10286,10288,10289,10292,10293,10294,10295,10297,10298,10299,10300,10302,10303,10305,10306,10307,10309,10310,10311,10312,10313,10314,10315] : List Nat)[i - 7798]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7810 ≤ i) (hii : i ≤ 7828) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10293,10294,10295,10297,10298,10299,10300,10302,10303,10305,10306,10307,10309,10310,10311,10312,10313,10314,10315] : List Nat)[i - 7810]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8288 ≤ i) (hii : i ≤ 8291) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10958,10959,10960,10963] : List Nat)[i - 8288]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8292 .JUMPDEST,
   pushAt 8293 1 12,
   opAt 8294 .XOR,
   pushAt 8295 2 10274,
   opAt 8296 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8292 .JUMPDEST,
   pushAt 8293 1 12,
   opAt 8294 .XOR,
   pushAt 8295 2 10274,
   opAt 8296 .JUMPI,
   pushAt 8297 0 0,
   opAt 8298 .CALLDATALOAD,
   pushAt 8299 1 32,
   opAt 8300 .CALLDATALOAD,
   opAt 8301 .ADD,
   pushAt 8302 1 96,
   opAt 8303 .ADD,
   opAt 8304 .CALLDATALOAD,
   pushAt 8305 1 160,
   opAt 8306 .SHR,
   pushAt 8307 2 902,
   opAt 8308 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8292 .JUMPDEST,
   pushAt 8293 1 12,
   opAt 8294 .XOR,
   pushAt 8295 2 10274,
   opAt 8296 .JUMPI,
   pushAt 8297 0 0,
   opAt 8298 .CALLDATALOAD,
   pushAt 8299 1 32,
   opAt 8300 .CALLDATALOAD,
   opAt 8301 .ADD,
   pushAt 8302 1 96,
   opAt 8303 .ADD,
   opAt 8304 .CALLDATALOAD,
   pushAt 8305 1 160,
   opAt 8306 .SHR,
   pushAt 8307 2 902,
   opAt 8308 .JUMPI,
   pushAt 8309 1 12,
   pushAt 8310 0 0,
   opAt 8311 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10964 = true :=
  CycleSubmission.Global.Binding.jumpDest 8292 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8292 ≤ i) (hii : i ≤ 8312) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10964,10965,10967,10968,10971,10972,10973,10974,10976,10977,10978,10980,10981,10982,10984,10985,10988,10989,10991,10992,10993] : List Nat)[i - 8292]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
