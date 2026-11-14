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
  [opAt 7832 .JUMPDEST,
   opAt 7833 (.Dup ⟨0,by decide⟩),
   pushAt 7834 2 10963,
   opAt 7835 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7832 .JUMPDEST,
   opAt 7833 (.Dup ⟨0,by decide⟩),
   pushAt 7834 2 10963,
   opAt 7835 .JUMPI,
   pushAt 7836 0 0,
   opAt 7837 .RETURN]
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
  [opAt 7801 .JUMPDEST,
   pushAt 7802 1 32,
   opAt 7803 .CALLDATALOAD,
   pushAt 7804 2 902,
   opAt 7805 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7801 .JUMPDEST,
   pushAt 7802 1 32,
   opAt 7803 .CALLDATALOAD,
   pushAt 7804 2 902,
   opAt 7805 .JUMPI,
   pushAt 7806 1 64,
   opAt 7807 .CALLDATALOAD,
   opAt 7808 (.Dup ⟨0,by decide⟩),
   pushAt 7809 1 32,
   opAt 7810 .LT,
   pushAt 7811 2 10957,
   opAt 7812 .JUMPI,
   opAt 8294 .JUMPDEST,
   opAt 8295 .POP,
   pushAt 8296 2 902,
   opAt 8297 .JUMP,
   opAt 637 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7801 .JUMPDEST,
   pushAt 7802 1 32,
   opAt 7803 .CALLDATALOAD,
   pushAt 7804 2 902,
   opAt 7805 .JUMPI,
   pushAt 7806 1 64,
   opAt 7807 .CALLDATALOAD,
   opAt 7808 (.Dup ⟨0,by decide⟩),
   pushAt 7809 1 32,
   opAt 7810 .LT,
   pushAt 7811 2 10957,
   opAt 7812 .JUMPI,
   pushAt 7813 0 0,
   opAt 7814 .CALLDATALOAD,
   pushAt 7815 1 96,
   opAt 7816 .ADD,
   opAt 7817 .CALLDATALOAD,
   opAt 7818 (.Dup ⟨1,by decide⟩),
   pushAt 7819 1 32,
   opAt 7820 .SUB,
   pushAt 7821 1 3,
   opAt 7822 .SHL,
   opAt 7823 .SHR,
   pushAt 7824 1 1,
   opAt 7825 .LT,
   pushAt 7826 0 0,
   opAt 7827 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7828 (.Dup ⟨0,by decide⟩),
   opAt 7829 .MSIZE,
   opAt 7830 .SUB,
   opAt 7831 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10302 = true :=
  CycleSubmission.Global.Binding.jumpDest 7801 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10957 = true :=
  CycleSubmission.Global.Binding.jumpDest 8294 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7832 ≤ i) (hii : i ≤ 7837) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10344,10345,10346,10349,10350,10351] : List Nat)[i - 7832]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7801 ≤ i) (hii : i ≤ 7831) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10302,10303,10305,10306,10309,10310,10312,10313,10314,10316,10317,10320,10321,10322,10323,10325,10326,10327,10328,10330,10331,10333,10334,10335,10337,10338,10339,10340,10341,10342,10343] : List Nat)[i - 7801]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7813 ≤ i) (hii : i ≤ 7831) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10321,10322,10323,10325,10326,10327,10328,10330,10331,10333,10334,10335,10337,10338,10339,10340,10341,10342,10343] : List Nat)[i - 7813]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8294 ≤ i) (hii : i ≤ 8297) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10957,10958,10959,10962] : List Nat)[i - 8294]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8298 .JUMPDEST,
   pushAt 8299 1 12,
   opAt 8300 .XOR,
   pushAt 8301 2 10302,
   opAt 8302 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8298 .JUMPDEST,
   pushAt 8299 1 12,
   opAt 8300 .XOR,
   pushAt 8301 2 10302,
   opAt 8302 .JUMPI,
   pushAt 8303 0 0,
   opAt 8304 .CALLDATALOAD,
   pushAt 8305 1 32,
   opAt 8306 .CALLDATALOAD,
   opAt 8307 .ADD,
   pushAt 8308 1 96,
   opAt 8309 .ADD,
   opAt 8310 .CALLDATALOAD,
   pushAt 8311 1 160,
   opAt 8312 .SHR,
   pushAt 8313 2 902,
   opAt 8314 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8298 .JUMPDEST,
   pushAt 8299 1 12,
   opAt 8300 .XOR,
   pushAt 8301 2 10302,
   opAt 8302 .JUMPI,
   pushAt 8303 0 0,
   opAt 8304 .CALLDATALOAD,
   pushAt 8305 1 32,
   opAt 8306 .CALLDATALOAD,
   opAt 8307 .ADD,
   pushAt 8308 1 96,
   opAt 8309 .ADD,
   opAt 8310 .CALLDATALOAD,
   pushAt 8311 1 160,
   opAt 8312 .SHR,
   pushAt 8313 2 902,
   opAt 8314 .JUMPI,
   pushAt 8315 1 12,
   pushAt 8316 0 0,
   opAt 8317 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10963 = true :=
  CycleSubmission.Global.Binding.jumpDest 8298 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8298 ≤ i) (hii : i ≤ 8318) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10963,10964,10966,10967,10970,10971,10972,10973,10975,10976,10977,10979,10980,10981,10983,10984,10987,10988,10990,10991,10992] : List Nat)[i - 8298]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
