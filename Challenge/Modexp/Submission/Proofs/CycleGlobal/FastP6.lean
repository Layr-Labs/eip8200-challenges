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
  [opAt 7913 .JUMPDEST,
   opAt 7914 (.Dup ⟨0,by decide⟩),
   pushAt 7915 2 10903,
   opAt 7916 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7913 .JUMPDEST,
   opAt 7914 (.Dup ⟨0,by decide⟩),
   pushAt 7915 2 10903,
   opAt 7916 .JUMPI,
   pushAt 7917 0 0,
   opAt 7918 .RETURN]
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
  [opAt 7882 .JUMPDEST,
   pushAt 7883 1 32,
   opAt 7884 .CALLDATALOAD,
   pushAt 7885 2 902,
   opAt 7886 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7882 .JUMPDEST,
   pushAt 7883 1 32,
   opAt 7884 .CALLDATALOAD,
   pushAt 7885 2 902,
   opAt 7886 .JUMPI,
   pushAt 7887 1 64,
   opAt 7888 .CALLDATALOAD,
   opAt 7889 (.Dup ⟨0,by decide⟩),
   pushAt 7890 1 32,
   opAt 7891 .LT,
   pushAt 7892 2 10897,
   opAt 7893 .JUMPI,
   opAt 8375 .JUMPDEST,
   opAt 8376 .POP,
   pushAt 8377 2 902,
   opAt 8378 .JUMP,
   opAt 637 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7882 .JUMPDEST,
   pushAt 7883 1 32,
   opAt 7884 .CALLDATALOAD,
   pushAt 7885 2 902,
   opAt 7886 .JUMPI,
   pushAt 7887 1 64,
   opAt 7888 .CALLDATALOAD,
   opAt 7889 (.Dup ⟨0,by decide⟩),
   pushAt 7890 1 32,
   opAt 7891 .LT,
   pushAt 7892 2 10897,
   opAt 7893 .JUMPI,
   pushAt 7894 0 0,
   opAt 7895 .CALLDATALOAD,
   pushAt 7896 1 96,
   opAt 7897 .ADD,
   opAt 7898 .CALLDATALOAD,
   opAt 7899 (.Dup ⟨1,by decide⟩),
   pushAt 7900 1 32,
   opAt 7901 .SUB,
   pushAt 7902 1 3,
   opAt 7903 .SHL,
   opAt 7904 .SHR,
   pushAt 7905 1 1,
   opAt 7906 .LT,
   pushAt 7907 0 0,
   opAt 7908 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7909 (.Dup ⟨0,by decide⟩),
   opAt 7910 .MSIZE,
   opAt 7911 .SUB,
   opAt 7912 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10242 = true :=
  CycleSubmission.Global.Binding.jumpDest 7882 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10897 = true :=
  CycleSubmission.Global.Binding.jumpDest 8375 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7913 ≤ i) (hii : i ≤ 7918) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10284,10285,10286,10289,10290,10291] : List Nat)[i - 7913]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7882 ≤ i) (hii : i ≤ 7912) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10242,10243,10245,10246,10249,10250,10252,10253,10254,10256,10257,10260,10261,10262,10263,10265,10266,10267,10268,10270,10271,10273,10274,10275,10277,10278,10279,10280,10281,10282,10283] : List Nat)[i - 7882]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7894 ≤ i) (hii : i ≤ 7912) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10261,10262,10263,10265,10266,10267,10268,10270,10271,10273,10274,10275,10277,10278,10279,10280,10281,10282,10283] : List Nat)[i - 7894]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8375 ≤ i) (hii : i ≤ 8378) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10897,10898,10899,10902] : List Nat)[i - 8375]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8379 .JUMPDEST,
   pushAt 8380 1 12,
   opAt 8381 .XOR,
   pushAt 8382 2 10242,
   opAt 8383 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8379 .JUMPDEST,
   pushAt 8380 1 12,
   opAt 8381 .XOR,
   pushAt 8382 2 10242,
   opAt 8383 .JUMPI,
   pushAt 8384 0 0,
   opAt 8385 .CALLDATALOAD,
   pushAt 8386 1 32,
   opAt 8387 .CALLDATALOAD,
   opAt 8388 .ADD,
   pushAt 8389 1 96,
   opAt 8390 .ADD,
   opAt 8391 .CALLDATALOAD,
   pushAt 8392 1 160,
   opAt 8393 .SHR,
   pushAt 8394 2 902,
   opAt 8395 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8379 .JUMPDEST,
   pushAt 8380 1 12,
   opAt 8381 .XOR,
   pushAt 8382 2 10242,
   opAt 8383 .JUMPI,
   pushAt 8384 0 0,
   opAt 8385 .CALLDATALOAD,
   pushAt 8386 1 32,
   opAt 8387 .CALLDATALOAD,
   opAt 8388 .ADD,
   pushAt 8389 1 96,
   opAt 8390 .ADD,
   opAt 8391 .CALLDATALOAD,
   pushAt 8392 1 160,
   opAt 8393 .SHR,
   pushAt 8394 2 902,
   opAt 8395 .JUMPI,
   pushAt 8396 1 12,
   pushAt 8397 0 0,
   opAt 8398 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10903 = true :=
  CycleSubmission.Global.Binding.jumpDest 8379 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8379 ≤ i) (hii : i ≤ 8399) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10903,10904,10906,10907,10910,10911,10912,10913,10915,10916,10917,10919,10920,10921,10923,10924,10927,10928,10930,10931,10932] : List Nat)[i - 8379]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
