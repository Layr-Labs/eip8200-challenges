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
  [opAt 7917 .JUMPDEST,
   opAt 7918 (.Dup ⟨0,by decide⟩),
   pushAt 7919 2 10911,
   opAt 7920 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7917 .JUMPDEST,
   opAt 7918 (.Dup ⟨0,by decide⟩),
   pushAt 7919 2 10911,
   opAt 7920 .JUMPI,
   pushAt 7921 0 0,
   opAt 7922 .RETURN]
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
  [opAt 7886 .JUMPDEST,
   pushAt 7887 1 32,
   opAt 7888 .CALLDATALOAD,
   pushAt 7889 2 902,
   opAt 7890 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7886 .JUMPDEST,
   pushAt 7887 1 32,
   opAt 7888 .CALLDATALOAD,
   pushAt 7889 2 902,
   opAt 7890 .JUMPI,
   pushAt 7891 1 64,
   opAt 7892 .CALLDATALOAD,
   opAt 7893 (.Dup ⟨0,by decide⟩),
   pushAt 7894 1 32,
   opAt 7895 .LT,
   pushAt 7896 2 10905,
   opAt 7897 .JUMPI,
   opAt 8379 .JUMPDEST,
   opAt 8380 .POP,
   pushAt 8381 2 902,
   opAt 8382 .JUMP,
   opAt 637 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7886 .JUMPDEST,
   pushAt 7887 1 32,
   opAt 7888 .CALLDATALOAD,
   pushAt 7889 2 902,
   opAt 7890 .JUMPI,
   pushAt 7891 1 64,
   opAt 7892 .CALLDATALOAD,
   opAt 7893 (.Dup ⟨0,by decide⟩),
   pushAt 7894 1 32,
   opAt 7895 .LT,
   pushAt 7896 2 10905,
   opAt 7897 .JUMPI,
   pushAt 7898 0 0,
   opAt 7899 .CALLDATALOAD,
   pushAt 7900 1 96,
   opAt 7901 .ADD,
   opAt 7902 .CALLDATALOAD,
   opAt 7903 (.Dup ⟨1,by decide⟩),
   pushAt 7904 1 32,
   opAt 7905 .SUB,
   pushAt 7906 1 3,
   opAt 7907 .SHL,
   opAt 7908 .SHR,
   pushAt 7909 1 1,
   opAt 7910 .LT,
   pushAt 7911 0 0,
   opAt 7912 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7913 (.Dup ⟨0,by decide⟩),
   opAt 7914 .MSIZE,
   opAt 7915 .SUB,
   opAt 7916 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10250 = true :=
  CycleSubmission.Global.Binding.jumpDest 7886 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10905 = true :=
  CycleSubmission.Global.Binding.jumpDest 8379 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7917 ≤ i) (hii : i ≤ 7922) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10292,10293,10294,10297,10298,10299] : List Nat)[i - 7917]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7886 ≤ i) (hii : i ≤ 7916) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10250,10251,10253,10254,10257,10258,10260,10261,10262,10264,10265,10268,10269,10270,10271,10273,10274,10275,10276,10278,10279,10281,10282,10283,10285,10286,10287,10288,10289,10290,10291] : List Nat)[i - 7886]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7898 ≤ i) (hii : i ≤ 7916) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10269,10270,10271,10273,10274,10275,10276,10278,10279,10281,10282,10283,10285,10286,10287,10288,10289,10290,10291] : List Nat)[i - 7898]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8379 ≤ i) (hii : i ≤ 8382) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10905,10906,10907,10910] : List Nat)[i - 8379]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8383 .JUMPDEST,
   pushAt 8384 1 12,
   opAt 8385 .XOR,
   pushAt 8386 2 10250,
   opAt 8387 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8383 .JUMPDEST,
   pushAt 8384 1 12,
   opAt 8385 .XOR,
   pushAt 8386 2 10250,
   opAt 8387 .JUMPI,
   pushAt 8388 0 0,
   opAt 8389 .CALLDATALOAD,
   pushAt 8390 1 32,
   opAt 8391 .CALLDATALOAD,
   opAt 8392 .ADD,
   pushAt 8393 1 96,
   opAt 8394 .ADD,
   opAt 8395 .CALLDATALOAD,
   pushAt 8396 1 160,
   opAt 8397 .SHR,
   pushAt 8398 2 902,
   opAt 8399 .JUMPI,
   opAt 637 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8383 .JUMPDEST,
   pushAt 8384 1 12,
   opAt 8385 .XOR,
   pushAt 8386 2 10250,
   opAt 8387 .JUMPI,
   pushAt 8388 0 0,
   opAt 8389 .CALLDATALOAD,
   pushAt 8390 1 32,
   opAt 8391 .CALLDATALOAD,
   opAt 8392 .ADD,
   pushAt 8393 1 96,
   opAt 8394 .ADD,
   opAt 8395 .CALLDATALOAD,
   pushAt 8396 1 160,
   opAt 8397 .SHR,
   pushAt 8398 2 902,
   opAt 8399 .JUMPI,
   pushAt 8400 1 12,
   pushAt 8401 0 0,
   opAt 8402 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10911 = true :=
  CycleSubmission.Global.Binding.jumpDest 8383 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8383 ≤ i) (hii : i ≤ 8403) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10911,10912,10914,10915,10918,10919,10920,10921,10923,10924,10925,10927,10928,10929,10931,10932,10935,10936,10938,10939,10940] : List Nat)[i - 8383]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
