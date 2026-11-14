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
  [opAt 7830 .JUMPDEST,
   opAt 7831 (.Dup ⟨0,by decide⟩),
   pushAt 7832 2 10961,
   opAt 7833 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7830 .JUMPDEST,
   opAt 7831 (.Dup ⟨0,by decide⟩),
   pushAt 7832 2 10961,
   opAt 7833 .JUMPI,
   pushAt 7834 0 0,
   opAt 7835 .RETURN]
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
  [opAt 7799 .JUMPDEST,
   pushAt 7800 1 32,
   opAt 7801 .CALLDATALOAD,
   pushAt 7802 2 902,
   opAt 7803 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7799 .JUMPDEST,
   pushAt 7800 1 32,
   opAt 7801 .CALLDATALOAD,
   pushAt 7802 2 902,
   opAt 7803 .JUMPI,
   pushAt 7804 1 64,
   opAt 7805 .CALLDATALOAD,
   opAt 7806 (.Dup ⟨0,by decide⟩),
   pushAt 7807 1 32,
   opAt 7808 .LT,
   pushAt 7809 2 10955,
   opAt 7810 .JUMPI,
   opAt 8290 .JUMPDEST,
   opAt 8291 .POP,
   pushAt 8292 2 902,
   opAt 8293 .JUMP,
   opAt 637 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7799 .JUMPDEST,
   pushAt 7800 1 32,
   opAt 7801 .CALLDATALOAD,
   pushAt 7802 2 902,
   opAt 7803 .JUMPI,
   pushAt 7804 1 64,
   opAt 7805 .CALLDATALOAD,
   opAt 7806 (.Dup ⟨0,by decide⟩),
   pushAt 7807 1 32,
   opAt 7808 .LT,
   pushAt 7809 2 10955,
   opAt 7810 .JUMPI,
   pushAt 7811 0 0,
   opAt 7812 .CALLDATALOAD,
   pushAt 7813 1 96,
   opAt 7814 .ADD,
   opAt 7815 .CALLDATALOAD,
   opAt 7816 (.Dup ⟨1,by decide⟩),
   pushAt 7817 1 32,
   opAt 7818 .SUB,
   pushAt 7819 1 3,
   opAt 7820 .SHL,
   opAt 7821 .SHR,
   pushAt 7822 1 1,
   opAt 7823 .LT,
   pushAt 7824 0 0,
   opAt 7825 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7826 (.Dup ⟨0,by decide⟩),
   opAt 7827 .MSIZE,
   opAt 7828 .SUB,
   opAt 7829 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10302 = true :=
  CycleSubmission.Global.Binding.jumpDest 7799 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10955 = true :=
  CycleSubmission.Global.Binding.jumpDest 8290 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7830 ≤ i) (hii : i ≤ 7835) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10344,10345,10346,10349,10350,10351] : List Nat)[i - 7830]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7799 ≤ i) (hii : i ≤ 7829) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10302,10303,10305,10306,10309,10310,10312,10313,10314,10316,10317,10320,10321,10322,10323,10325,10326,10327,10328,10330,10331,10333,10334,10335,10337,10338,10339,10340,10341,10342,10343] : List Nat)[i - 7799]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7811 ≤ i) (hii : i ≤ 7829) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10321,10322,10323,10325,10326,10327,10328,10330,10331,10333,10334,10335,10337,10338,10339,10340,10341,10342,10343] : List Nat)[i - 7811]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8290 ≤ i) (hii : i ≤ 8293) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10955,10956,10957,10960] : List Nat)[i - 8290]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8294 .JUMPDEST,
   pushAt 8295 1 12,
   opAt 8296 .XOR,
   pushAt 8297 2 10302,
   opAt 8298 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8294 .JUMPDEST,
   pushAt 8295 1 12,
   opAt 8296 .XOR,
   pushAt 8297 2 10302,
   opAt 8298 .JUMPI,
   pushAt 8299 0 0,
   opAt 8300 .CALLDATALOAD,
   pushAt 8301 1 32,
   opAt 8302 .CALLDATALOAD,
   opAt 8303 .ADD,
   pushAt 8304 1 96,
   opAt 8305 .ADD,
   opAt 8306 .CALLDATALOAD,
   pushAt 8307 1 160,
   opAt 8308 .SHR,
   pushAt 8309 2 902,
   opAt 8310 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8294 .JUMPDEST,
   pushAt 8295 1 12,
   opAt 8296 .XOR,
   pushAt 8297 2 10302,
   opAt 8298 .JUMPI,
   pushAt 8299 0 0,
   opAt 8300 .CALLDATALOAD,
   pushAt 8301 1 32,
   opAt 8302 .CALLDATALOAD,
   opAt 8303 .ADD,
   pushAt 8304 1 96,
   opAt 8305 .ADD,
   opAt 8306 .CALLDATALOAD,
   pushAt 8307 1 160,
   opAt 8308 .SHR,
   pushAt 8309 2 902,
   opAt 8310 .JUMPI,
   pushAt 8311 1 12,
   pushAt 8312 0 0,
   opAt 8313 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10961 = true :=
  CycleSubmission.Global.Binding.jumpDest 8294 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8294 ≤ i) (hii : i ≤ 8314) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10961,10962,10964,10965,10968,10969,10970,10971,10973,10974,10975,10977,10978,10979,10981,10982,10985,10986,10988,10989,10990] : List Nat)[i - 8294]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
