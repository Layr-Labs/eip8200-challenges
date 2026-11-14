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
  [opAt 7844 .JUMPDEST,
   opAt 7845 (.Dup ⟨0,by decide⟩),
   pushAt 7846 2 10843,
   opAt 7847 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7844 .JUMPDEST,
   opAt 7845 (.Dup ⟨0,by decide⟩),
   pushAt 7846 2 10843,
   opAt 7847 .JUMPI,
   pushAt 7848 0 0,
   opAt 7849 .RETURN]
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
  [opAt 7813 .JUMPDEST,
   pushAt 7814 1 32,
   opAt 7815 .CALLDATALOAD,
   pushAt 7816 2 902,
   opAt 7817 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7813 .JUMPDEST,
   pushAt 7814 1 32,
   opAt 7815 .CALLDATALOAD,
   pushAt 7816 2 902,
   opAt 7817 .JUMPI,
   pushAt 7818 1 64,
   opAt 7819 .CALLDATALOAD,
   opAt 7820 (.Dup ⟨0,by decide⟩),
   pushAt 7821 1 32,
   opAt 7822 .LT,
   pushAt 7823 2 10837,
   opAt 7824 .JUMPI,
   opAt 8308 .JUMPDEST,
   opAt 8309 .POP,
   pushAt 8310 2 902,
   opAt 8311 .JUMP,
   opAt 637 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7813 .JUMPDEST,
   pushAt 7814 1 32,
   opAt 7815 .CALLDATALOAD,
   pushAt 7816 2 902,
   opAt 7817 .JUMPI,
   pushAt 7818 1 64,
   opAt 7819 .CALLDATALOAD,
   opAt 7820 (.Dup ⟨0,by decide⟩),
   pushAt 7821 1 32,
   opAt 7822 .LT,
   pushAt 7823 2 10837,
   opAt 7824 .JUMPI,
   pushAt 7825 0 0,
   opAt 7826 .CALLDATALOAD,
   pushAt 7827 1 96,
   opAt 7828 .ADD,
   opAt 7829 .CALLDATALOAD,
   opAt 7830 (.Dup ⟨1,by decide⟩),
   pushAt 7831 1 32,
   opAt 7832 .SUB,
   pushAt 7833 1 3,
   opAt 7834 .SHL,
   opAt 7835 .SHR,
   pushAt 7836 1 1,
   opAt 7837 .LT,
   pushAt 7838 0 0,
   opAt 7839 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7840 (.Dup ⟨0,by decide⟩),
   opAt 7841 .MSIZE,
   opAt 7842 .SUB,
   opAt 7843 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10180 = true :=
  CycleSubmission.Global.Binding.jumpDest 7813 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10837 = true :=
  CycleSubmission.Global.Binding.jumpDest 8308 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7844 ≤ i) (hii : i ≤ 7849) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10222,10223,10224,10227,10228,10229] : List Nat)[i - 7844]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7813 ≤ i) (hii : i ≤ 7843) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10180,10181,10183,10184,10187,10188,10190,10191,10192,10194,10195,10198,10199,10200,10201,10203,10204,10205,10206,10208,10209,10211,10212,10213,10215,10216,10217,10218,10219,10220,10221] : List Nat)[i - 7813]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7825 ≤ i) (hii : i ≤ 7843) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10199,10200,10201,10203,10204,10205,10206,10208,10209,10211,10212,10213,10215,10216,10217,10218,10219,10220,10221] : List Nat)[i - 7825]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8308 ≤ i) (hii : i ≤ 8311) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10837,10838,10839,10842] : List Nat)[i - 8308]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8312 .JUMPDEST,
   pushAt 8313 1 12,
   opAt 8314 .XOR,
   pushAt 8315 2 10180,
   opAt 8316 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8312 .JUMPDEST,
   pushAt 8313 1 12,
   opAt 8314 .XOR,
   pushAt 8315 2 10180,
   opAt 8316 .JUMPI,
   pushAt 8317 0 0,
   opAt 8318 .CALLDATALOAD,
   pushAt 8319 1 32,
   opAt 8320 .CALLDATALOAD,
   opAt 8321 .ADD,
   pushAt 8322 1 96,
   opAt 8323 .ADD,
   opAt 8324 .CALLDATALOAD,
   pushAt 8325 1 160,
   opAt 8326 .SHR,
   pushAt 8327 2 902,
   opAt 8328 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8312 .JUMPDEST,
   pushAt 8313 1 12,
   opAt 8314 .XOR,
   pushAt 8315 2 10180,
   opAt 8316 .JUMPI,
   pushAt 8317 0 0,
   opAt 8318 .CALLDATALOAD,
   pushAt 8319 1 32,
   opAt 8320 .CALLDATALOAD,
   opAt 8321 .ADD,
   pushAt 8322 1 96,
   opAt 8323 .ADD,
   opAt 8324 .CALLDATALOAD,
   pushAt 8325 1 160,
   opAt 8326 .SHR,
   pushAt 8327 2 902,
   opAt 8328 .JUMPI,
   pushAt 8329 1 12,
   pushAt 8330 0 0,
   opAt 8331 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10843 = true :=
  CycleSubmission.Global.Binding.jumpDest 8312 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8312 ≤ i) (hii : i ≤ 8332) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10843,10844,10846,10847,10850,10851,10852,10853,10855,10856,10857,10859,10860,10861,10863,10864,10867,10868,10870,10871,10872] : List Nat)[i - 8312]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
