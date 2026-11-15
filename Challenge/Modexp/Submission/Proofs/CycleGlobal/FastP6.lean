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
  [opAt 7825 .JUMPDEST,
   opAt 7826 (.Dup ⟨0,by decide⟩),
   pushAt 7827 2 10959,
   opAt 7828 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7825 .JUMPDEST,
   opAt 7826 (.Dup ⟨0,by decide⟩),
   pushAt 7827 2 10959,
   opAt 7828 .JUMPI,
   pushAt 7829 0 0,
   opAt 7830 .RETURN]
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
  [opAt 7794 .JUMPDEST,
   pushAt 7795 1 32,
   opAt 7796 .CALLDATALOAD,
   pushAt 7797 2 902,
   opAt 7798 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7794 .JUMPDEST,
   pushAt 7795 1 32,
   opAt 7796 .CALLDATALOAD,
   pushAt 7797 2 902,
   opAt 7798 .JUMPI,
   pushAt 7799 1 64,
   opAt 7800 .CALLDATALOAD,
   opAt 7801 (.Dup ⟨0,by decide⟩),
   pushAt 7802 1 32,
   opAt 7803 .LT,
   pushAt 7804 2 10953,
   opAt 7805 .JUMPI,
   opAt 8283 .JUMPDEST,
   opAt 8284 .POP,
   pushAt 8285 2 902,
   opAt 8286 .JUMP,
   opAt 637 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7794 .JUMPDEST,
   pushAt 7795 1 32,
   opAt 7796 .CALLDATALOAD,
   pushAt 7797 2 902,
   opAt 7798 .JUMPI,
   pushAt 7799 1 64,
   opAt 7800 .CALLDATALOAD,
   opAt 7801 (.Dup ⟨0,by decide⟩),
   pushAt 7802 1 32,
   opAt 7803 .LT,
   pushAt 7804 2 10953,
   opAt 7805 .JUMPI,
   pushAt 7806 0 0,
   opAt 7807 .CALLDATALOAD,
   pushAt 7808 1 96,
   opAt 7809 .ADD,
   opAt 7810 .CALLDATALOAD,
   opAt 7811 (.Dup ⟨1,by decide⟩),
   pushAt 7812 1 32,
   opAt 7813 .SUB,
   pushAt 7814 1 3,
   opAt 7815 .SHL,
   opAt 7816 .SHR,
   pushAt 7817 1 1,
   opAt 7818 .LT,
   pushAt 7819 0 0,
   opAt 7820 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7821 (.Dup ⟨0,by decide⟩),
   opAt 7822 .MSIZE,
   opAt 7823 .SUB,
   opAt 7824 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10302 = true :=
  CycleSubmission.Global.Binding.jumpDest 7794 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10953 = true :=
  CycleSubmission.Global.Binding.jumpDest 8283 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7825 ≤ i) (hii : i ≤ 7830) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10344,10345,10346,10349,10350,10351] : List Nat)[i - 7825]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7794 ≤ i) (hii : i ≤ 7824) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10302,10303,10305,10306,10309,10310,10312,10313,10314,10316,10317,10320,10321,10322,10323,10325,10326,10327,10328,10330,10331,10333,10334,10335,10337,10338,10339,10340,10341,10342,10343] : List Nat)[i - 7794]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7806 ≤ i) (hii : i ≤ 7824) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10321,10322,10323,10325,10326,10327,10328,10330,10331,10333,10334,10335,10337,10338,10339,10340,10341,10342,10343] : List Nat)[i - 7806]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8283 ≤ i) (hii : i ≤ 8286) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10953,10954,10955,10958] : List Nat)[i - 8283]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8287 .JUMPDEST,
   pushAt 8288 1 12,
   opAt 8289 .XOR,
   pushAt 8290 2 10302,
   opAt 8291 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8287 .JUMPDEST,
   pushAt 8288 1 12,
   opAt 8289 .XOR,
   pushAt 8290 2 10302,
   opAt 8291 .JUMPI,
   pushAt 8292 0 0,
   opAt 8293 .CALLDATALOAD,
   pushAt 8294 1 32,
   opAt 8295 .CALLDATALOAD,
   opAt 8296 .ADD,
   pushAt 8297 1 96,
   opAt 8298 .ADD,
   opAt 8299 .CALLDATALOAD,
   pushAt 8300 1 160,
   opAt 8301 .SHR,
   pushAt 8302 2 902,
   opAt 8303 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8287 .JUMPDEST,
   pushAt 8288 1 12,
   opAt 8289 .XOR,
   pushAt 8290 2 10302,
   opAt 8291 .JUMPI,
   pushAt 8292 0 0,
   opAt 8293 .CALLDATALOAD,
   pushAt 8294 1 32,
   opAt 8295 .CALLDATALOAD,
   opAt 8296 .ADD,
   pushAt 8297 1 96,
   opAt 8298 .ADD,
   opAt 8299 .CALLDATALOAD,
   pushAt 8300 1 160,
   opAt 8301 .SHR,
   pushAt 8302 2 902,
   opAt 8303 .JUMPI,
   pushAt 8304 1 12,
   pushAt 8305 0 0,
   opAt 8306 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10959 = true :=
  CycleSubmission.Global.Binding.jumpDest 8287 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8287 ≤ i) (hii : i ≤ 8315) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10959,10960,10962,10963,10966,10967,10968,10969,10971,10972,10973,10975,10976,10977,10979,10980,10983,10984,10986,10987,10988,10989,10990,10991,10992,10993,10994,10995,10996] : List Nat)[i - 8287]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
