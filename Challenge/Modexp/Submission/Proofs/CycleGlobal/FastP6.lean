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
  [opAt 7834 .JUMPDEST,
   opAt 7835 (.Dup ⟨0,by decide⟩),
   pushAt 7836 2 10907,
   opAt 7837 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7834 .JUMPDEST,
   opAt 7835 (.Dup ⟨0,by decide⟩),
   pushAt 7836 2 10907,
   opAt 7837 .JUMPI,
   pushAt 7838 0 0,
   opAt 7839 .RETURN]
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
  [opAt 7803 .JUMPDEST,
   pushAt 7804 1 32,
   opAt 7805 .CALLDATALOAD,
   pushAt 7806 2 902,
   opAt 7807 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7803 .JUMPDEST,
   pushAt 7804 1 32,
   opAt 7805 .CALLDATALOAD,
   pushAt 7806 2 902,
   opAt 7807 .JUMPI,
   pushAt 7808 1 64,
   opAt 7809 .CALLDATALOAD,
   opAt 7810 (.Dup ⟨0,by decide⟩),
   pushAt 7811 1 32,
   opAt 7812 .LT,
   pushAt 7813 2 10901,
   opAt 7814 .JUMPI,
   opAt 8296 .JUMPDEST,
   opAt 8297 .POP,
   pushAt 8298 2 902,
   opAt 8299 .JUMP,
   opAt 637 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7803 .JUMPDEST,
   pushAt 7804 1 32,
   opAt 7805 .CALLDATALOAD,
   pushAt 7806 2 902,
   opAt 7807 .JUMPI,
   pushAt 7808 1 64,
   opAt 7809 .CALLDATALOAD,
   opAt 7810 (.Dup ⟨0,by decide⟩),
   pushAt 7811 1 32,
   opAt 7812 .LT,
   pushAt 7813 2 10901,
   opAt 7814 .JUMPI,
   pushAt 7815 0 0,
   opAt 7816 .CALLDATALOAD,
   pushAt 7817 1 96,
   opAt 7818 .ADD,
   opAt 7819 .CALLDATALOAD,
   opAt 7820 (.Dup ⟨1,by decide⟩),
   pushAt 7821 1 32,
   opAt 7822 .SUB,
   pushAt 7823 1 3,
   opAt 7824 .SHL,
   opAt 7825 .SHR,
   pushAt 7826 1 1,
   opAt 7827 .LT,
   pushAt 7828 0 0,
   opAt 7829 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7830 (.Dup ⟨0,by decide⟩),
   opAt 7831 .MSIZE,
   opAt 7832 .SUB,
   opAt 7833 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10246 = true :=
  CycleSubmission.Global.Binding.jumpDest 7803 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10901 = true :=
  CycleSubmission.Global.Binding.jumpDest 8296 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7834 ≤ i) (hii : i ≤ 7839) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10288,10289,10290,10293,10294,10295] : List Nat)[i - 7834]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7803 ≤ i) (hii : i ≤ 7833) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10246,10247,10249,10250,10253,10254,10256,10257,10258,10260,10261,10264,10265,10266,10267,10269,10270,10271,10272,10274,10275,10277,10278,10279,10281,10282,10283,10284,10285,10286,10287] : List Nat)[i - 7803]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7815 ≤ i) (hii : i ≤ 7833) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10265,10266,10267,10269,10270,10271,10272,10274,10275,10277,10278,10279,10281,10282,10283,10284,10285,10286,10287] : List Nat)[i - 7815]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8296 ≤ i) (hii : i ≤ 8299) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10901,10902,10903,10906] : List Nat)[i - 8296]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8300 .JUMPDEST,
   pushAt 8301 1 12,
   opAt 8302 .XOR,
   pushAt 8303 2 10246,
   opAt 8304 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8300 .JUMPDEST,
   pushAt 8301 1 12,
   opAt 8302 .XOR,
   pushAt 8303 2 10246,
   opAt 8304 .JUMPI,
   pushAt 8305 0 0,
   opAt 8306 .CALLDATALOAD,
   pushAt 8307 1 32,
   opAt 8308 .CALLDATALOAD,
   opAt 8309 .ADD,
   pushAt 8310 1 96,
   opAt 8311 .ADD,
   opAt 8312 .CALLDATALOAD,
   pushAt 8313 1 160,
   opAt 8314 .SHR,
   pushAt 8315 2 902,
   opAt 8316 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8300 .JUMPDEST,
   pushAt 8301 1 12,
   opAt 8302 .XOR,
   pushAt 8303 2 10246,
   opAt 8304 .JUMPI,
   pushAt 8305 0 0,
   opAt 8306 .CALLDATALOAD,
   pushAt 8307 1 32,
   opAt 8308 .CALLDATALOAD,
   opAt 8309 .ADD,
   pushAt 8310 1 96,
   opAt 8311 .ADD,
   opAt 8312 .CALLDATALOAD,
   pushAt 8313 1 160,
   opAt 8314 .SHR,
   pushAt 8315 2 902,
   opAt 8316 .JUMPI,
   pushAt 8317 1 12,
   pushAt 8318 0 0,
   opAt 8319 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10907 = true :=
  CycleSubmission.Global.Binding.jumpDest 8300 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8300 ≤ i) (hii : i ≤ 8320) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10907,10908,10910,10911,10914,10915,10916,10917,10919,10920,10921,10923,10924,10925,10927,10928,10931,10932,10934,10935,10936] : List Nat)[i - 8300]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
