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
  [opAt 7828 .JUMPDEST,
   opAt 7829 (.Dup ⟨0,by decide⟩),
   pushAt 7830 2 10959,
   opAt 7831 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7828 .JUMPDEST,
   opAt 7829 (.Dup ⟨0,by decide⟩),
   pushAt 7830 2 10959,
   opAt 7831 .JUMPI,
   pushAt 7832 0 0,
   opAt 7833 .RETURN]
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
  [opAt 7797 .JUMPDEST,
   pushAt 7798 1 32,
   opAt 7799 .CALLDATALOAD,
   pushAt 7800 2 902,
   opAt 7801 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7797 .JUMPDEST,
   pushAt 7798 1 32,
   opAt 7799 .CALLDATALOAD,
   pushAt 7800 2 902,
   opAt 7801 .JUMPI,
   pushAt 7802 1 64,
   opAt 7803 .CALLDATALOAD,
   opAt 7804 (.Dup ⟨0,by decide⟩),
   pushAt 7805 1 32,
   opAt 7806 .LT,
   pushAt 7807 2 10953,
   opAt 7808 .JUMPI,
   opAt 8286 .JUMPDEST,
   opAt 8287 .POP,
   pushAt 8288 2 902,
   opAt 8289 .JUMP,
   opAt 637 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7797 .JUMPDEST,
   pushAt 7798 1 32,
   opAt 7799 .CALLDATALOAD,
   pushAt 7800 2 902,
   opAt 7801 .JUMPI,
   pushAt 7802 1 64,
   opAt 7803 .CALLDATALOAD,
   opAt 7804 (.Dup ⟨0,by decide⟩),
   pushAt 7805 1 32,
   opAt 7806 .LT,
   pushAt 7807 2 10953,
   opAt 7808 .JUMPI,
   pushAt 7809 0 0,
   opAt 7810 .CALLDATALOAD,
   pushAt 7811 1 96,
   opAt 7812 .ADD,
   opAt 7813 .CALLDATALOAD,
   opAt 7814 (.Dup ⟨1,by decide⟩),
   pushAt 7815 1 32,
   opAt 7816 .SUB,
   pushAt 7817 1 3,
   opAt 7818 .SHL,
   opAt 7819 .SHR,
   pushAt 7820 1 1,
   opAt 7821 .LT,
   pushAt 7822 0 0,
   opAt 7823 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7824 (.Dup ⟨0,by decide⟩),
   opAt 7825 .MSIZE,
   opAt 7826 .SUB,
   opAt 7827 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10302 = true :=
  CycleSubmission.Global.Binding.jumpDest 7797 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10953 = true :=
  CycleSubmission.Global.Binding.jumpDest 8286 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7828 ≤ i) (hii : i ≤ 7833) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10344,10345,10346,10349,10350,10351] : List Nat)[i - 7828]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7797 ≤ i) (hii : i ≤ 7827) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10302,10303,10305,10306,10309,10310,10312,10313,10314,10316,10317,10320,10321,10322,10323,10325,10326,10327,10328,10330,10331,10333,10334,10335,10337,10338,10339,10340,10341,10342,10343] : List Nat)[i - 7797]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7809 ≤ i) (hii : i ≤ 7827) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10321,10322,10323,10325,10326,10327,10328,10330,10331,10333,10334,10335,10337,10338,10339,10340,10341,10342,10343] : List Nat)[i - 7809]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8286 ≤ i) (hii : i ≤ 8289) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10953,10954,10955,10958] : List Nat)[i - 8286]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8290 .JUMPDEST,
   pushAt 8291 1 12,
   opAt 8292 .XOR,
   pushAt 8293 2 10302,
   opAt 8294 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8290 .JUMPDEST,
   pushAt 8291 1 12,
   opAt 8292 .XOR,
   pushAt 8293 2 10302,
   opAt 8294 .JUMPI,
   pushAt 8295 0 0,
   opAt 8296 .CALLDATALOAD,
   pushAt 8297 1 32,
   opAt 8298 .CALLDATALOAD,
   opAt 8299 .ADD,
   pushAt 8300 1 96,
   opAt 8301 .ADD,
   opAt 8302 .CALLDATALOAD,
   pushAt 8303 1 160,
   opAt 8304 .SHR,
   pushAt 8305 2 902,
   opAt 8306 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8290 .JUMPDEST,
   pushAt 8291 1 12,
   opAt 8292 .XOR,
   pushAt 8293 2 10302,
   opAt 8294 .JUMPI,
   pushAt 8295 0 0,
   opAt 8296 .CALLDATALOAD,
   pushAt 8297 1 32,
   opAt 8298 .CALLDATALOAD,
   opAt 8299 .ADD,
   pushAt 8300 1 96,
   opAt 8301 .ADD,
   opAt 8302 .CALLDATALOAD,
   pushAt 8303 1 160,
   opAt 8304 .SHR,
   pushAt 8305 2 902,
   opAt 8306 .JUMPI,
   pushAt 8307 1 12,
   pushAt 8308 0 0,
   opAt 8309 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10959 = true :=
  CycleSubmission.Global.Binding.jumpDest 8290 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8290 ≤ i) (hii : i ≤ 8318) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10959,10960,10962,10963,10966,10967,10968,10969,10971,10972,10973,10975,10976,10977,10979,10980,10983,10984,10986,10987,10988,10989,10990,10991,10992,10993,10994,10995,10996] : List Nat)[i - 8290]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
