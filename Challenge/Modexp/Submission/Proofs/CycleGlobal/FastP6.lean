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
  [opAt 7836 .JUMPDEST,
   opAt 7837 (.Dup ⟨0,by decide⟩),
   pushAt 7838 2 10907,
   opAt 7839 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7836 .JUMPDEST,
   opAt 7837 (.Dup ⟨0,by decide⟩),
   pushAt 7838 2 10907,
   opAt 7839 .JUMPI,
   pushAt 7840 0 0,
   opAt 7841 .RETURN]
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
  [opAt 7805 .JUMPDEST,
   pushAt 7806 1 32,
   opAt 7807 .CALLDATALOAD,
   pushAt 7808 2 902,
   opAt 7809 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7805 .JUMPDEST,
   pushAt 7806 1 32,
   opAt 7807 .CALLDATALOAD,
   pushAt 7808 2 902,
   opAt 7809 .JUMPI,
   pushAt 7810 1 64,
   opAt 7811 .CALLDATALOAD,
   opAt 7812 (.Dup ⟨0,by decide⟩),
   pushAt 7813 1 32,
   opAt 7814 .LT,
   pushAt 7815 2 10901,
   opAt 7816 .JUMPI,
   opAt 8298 .JUMPDEST,
   opAt 8299 .POP,
   pushAt 8300 2 902,
   opAt 8301 .JUMP,
   opAt 637 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7805 .JUMPDEST,
   pushAt 7806 1 32,
   opAt 7807 .CALLDATALOAD,
   pushAt 7808 2 902,
   opAt 7809 .JUMPI,
   pushAt 7810 1 64,
   opAt 7811 .CALLDATALOAD,
   opAt 7812 (.Dup ⟨0,by decide⟩),
   pushAt 7813 1 32,
   opAt 7814 .LT,
   pushAt 7815 2 10901,
   opAt 7816 .JUMPI,
   pushAt 7817 0 0,
   opAt 7818 .CALLDATALOAD,
   pushAt 7819 1 96,
   opAt 7820 .ADD,
   opAt 7821 .CALLDATALOAD,
   opAt 7822 (.Dup ⟨1,by decide⟩),
   pushAt 7823 1 32,
   opAt 7824 .SUB,
   pushAt 7825 1 3,
   opAt 7826 .SHL,
   opAt 7827 .SHR,
   pushAt 7828 1 1,
   opAt 7829 .LT,
   pushAt 7830 0 0,
   opAt 7831 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7832 (.Dup ⟨0,by decide⟩),
   opAt 7833 .MSIZE,
   opAt 7834 .SUB,
   opAt 7835 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10246 = true :=
  CycleSubmission.Global.Binding.jumpDest 7805 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10901 = true :=
  CycleSubmission.Global.Binding.jumpDest 8298 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7836 ≤ i) (hii : i ≤ 7841) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10288,10289,10290,10293,10294,10295] : List Nat)[i - 7836]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7805 ≤ i) (hii : i ≤ 7835) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10246,10247,10249,10250,10253,10254,10256,10257,10258,10260,10261,10264,10265,10266,10267,10269,10270,10271,10272,10274,10275,10277,10278,10279,10281,10282,10283,10284,10285,10286,10287] : List Nat)[i - 7805]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7817 ≤ i) (hii : i ≤ 7835) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10265,10266,10267,10269,10270,10271,10272,10274,10275,10277,10278,10279,10281,10282,10283,10284,10285,10286,10287] : List Nat)[i - 7817]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8298 ≤ i) (hii : i ≤ 8301) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10901,10902,10903,10906] : List Nat)[i - 8298]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8302 .JUMPDEST,
   pushAt 8303 1 12,
   opAt 8304 .XOR,
   pushAt 8305 2 10246,
   opAt 8306 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8302 .JUMPDEST,
   pushAt 8303 1 12,
   opAt 8304 .XOR,
   pushAt 8305 2 10246,
   opAt 8306 .JUMPI,
   pushAt 8307 0 0,
   opAt 8308 .CALLDATALOAD,
   pushAt 8309 1 32,
   opAt 8310 .CALLDATALOAD,
   opAt 8311 .ADD,
   pushAt 8312 1 96,
   opAt 8313 .ADD,
   opAt 8314 .CALLDATALOAD,
   pushAt 8315 1 160,
   opAt 8316 .SHR,
   pushAt 8317 2 902,
   opAt 8318 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8302 .JUMPDEST,
   pushAt 8303 1 12,
   opAt 8304 .XOR,
   pushAt 8305 2 10246,
   opAt 8306 .JUMPI,
   pushAt 8307 0 0,
   opAt 8308 .CALLDATALOAD,
   pushAt 8309 1 32,
   opAt 8310 .CALLDATALOAD,
   opAt 8311 .ADD,
   pushAt 8312 1 96,
   opAt 8313 .ADD,
   opAt 8314 .CALLDATALOAD,
   pushAt 8315 1 160,
   opAt 8316 .SHR,
   pushAt 8317 2 902,
   opAt 8318 .JUMPI,
   pushAt 8319 1 12,
   pushAt 8320 0 0,
   opAt 8321 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10907 = true :=
  CycleSubmission.Global.Binding.jumpDest 8302 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8302 ≤ i) (hii : i ≤ 8322) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10907,10908,10910,10911,10914,10915,10916,10917,10919,10920,10921,10923,10924,10925,10927,10928,10931,10932,10934,10935,10936] : List Nat)[i - 8302]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
