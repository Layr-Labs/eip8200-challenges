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
/-- The empty-modulus test at pc 3716 (instructions 511..513, in the former unreachable
filler behind the memo hit exit) for a nonzero `msize`: `JUMPDEST PUSH2 3671 JUMPI`
consumes `msize` and lands on the zero-exponent test appended at pc 3671 with an
empty stack. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7980 .JUMPDEST,
   opAt 7981 (.Dup ⟨0,by decide⟩),
   pushAt 7982 2 10966,
   opAt 7983 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7980 .JUMPDEST,
   opAt 7981 (.Dup ⟨0,by decide⟩),
   pushAt 7982 2 10966,
   opAt 7983 .JUMPI,
   pushAt 7984 0 0,
   opAt 7985 .RETURN]
/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/
/-- The zero-exponent test appended at pc 3671 (instructions 8638..8642) for a nonzero
`esize`: `JUMPDEST PUSH1 32 CALLDATALOAD PUSH2 698 JUMPI` lands on the `JUMPDEST` at
pc 698 (instruction 488), which falls into the fixed-vector recogniser at pc 699 with an
empty stack. -/
def blkZeroExpMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7949 .JUMPDEST,
   pushAt 7950 1 32,
   opAt 7951 .CALLDATALOAD,
   pushAt 7952 2 863,
   opAt 7953 .JUMPI,
   opAt 630 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7949 .JUMPDEST,
   pushAt 7950 1 32,
   opAt 7951 .CALLDATALOAD,
   pushAt 7952 2 863,
   opAt 7953 .JUMPI,
   pushAt 7954 1 64,
   opAt 7955 .CALLDATALOAD,
   opAt 7956 (.Dup ⟨0,by decide⟩),
   pushAt 7957 1 32,
   opAt 7958 .LT,
   pushAt 7959 2 10960,
   opAt 7960 .JUMPI,
   opAt 8259 .JUMPDEST,
   opAt 8260 .POP,
   pushAt 8261 2 863,
   opAt 8262 .JUMP,
   opAt 630 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7949 .JUMPDEST,
   pushAt 7950 1 32,
   opAt 7951 .CALLDATALOAD,
   pushAt 7952 2 863,
   opAt 7953 .JUMPI,
   pushAt 7954 1 64,
   opAt 7955 .CALLDATALOAD,
   opAt 7956 (.Dup ⟨0,by decide⟩),
   pushAt 7957 1 32,
   opAt 7958 .LT,
   pushAt 7959 2 10960,
   opAt 7960 .JUMPI,
   pushAt 7961 0 0,
   opAt 7962 .CALLDATALOAD,
   pushAt 7963 1 96,
   opAt 7964 .ADD,
   opAt 7965 .CALLDATALOAD,
   opAt 7966 (.Dup ⟨1,by decide⟩),
   pushAt 7967 1 32,
   opAt 7968 .SUB,
   pushAt 7969 1 3,
   opAt 7970 .SHL,
   opAt 7971 .SHR,
   pushAt 7972 1 1,
   opAt 7973 .LT,
   pushAt 7974 0 0,
   opAt 7975 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7976 (.Dup ⟨0,by decide⟩),
   opAt 7977 .MSIZE,
   opAt 7978 .SUB,
   opAt 7979 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10526 = true :=
  CycleSubmission.Global.Binding.jumpDest 7949 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10960 = true :=
  CycleSubmission.Global.Binding.jumpDest 8259 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7980 ≤ i) (hii : i ≤ 7985) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10568,10569,10570,10573,10574,10575] : List Nat)[i - 7980]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7949 ≤ i) (hii : i ≤ 7979) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10526,10527,10529,10530,10533,10534,10536,10537,10538,10540,10541,10544,10545,10546,10547,10549,10550,10551,10552,10554,10555,10557,10558,10559,10561,10562,10563,10564,10565,10566,10567] : List Nat)[i - 7949]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7961 ≤ i) (hii : i ≤ 7979) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10545,10546,10547,10549,10550,10551,10552,10554,10555,10557,10558,10559,10561,10562,10563,10564,10565,10566,10567] : List Nat)[i - 7961]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8259 ≤ i) (hii : i ≤ 8262) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10960,10961,10962,10965] : List Nat)[i - 8259]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8263 .JUMPDEST,
   pushAt 8264 1 12,
   opAt 8265 .XOR,
   pushAt 8266 2 10526,
   opAt 8267 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8263 .JUMPDEST,
   pushAt 8264 1 12,
   opAt 8265 .XOR,
   pushAt 8266 2 10526,
   opAt 8267 .JUMPI,
   pushAt 8268 0 0,
   opAt 8269 .CALLDATALOAD,
   pushAt 8270 1 32,
   opAt 8271 .CALLDATALOAD,
   opAt 8272 .ADD,
   pushAt 8273 1 96,
   opAt 8274 .ADD,
   opAt 8275 .CALLDATALOAD,
   pushAt 8276 1 160,
   opAt 8277 .SHR,
   pushAt 8278 2 863,
   opAt 8279 .JUMPI,
   opAt 630 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8263 .JUMPDEST,
   pushAt 8264 1 12,
   opAt 8265 .XOR,
   pushAt 8266 2 10526,
   opAt 8267 .JUMPI,
   pushAt 8268 0 0,
   opAt 8269 .CALLDATALOAD,
   pushAt 8270 1 32,
   opAt 8271 .CALLDATALOAD,
   opAt 8272 .ADD,
   pushAt 8273 1 96,
   opAt 8274 .ADD,
   opAt 8275 .CALLDATALOAD,
   pushAt 8276 1 160,
   opAt 8277 .SHR,
   pushAt 8278 2 863,
   opAt 8279 .JUMPI,
   pushAt 8280 1 12,
   pushAt 8281 0 0,
   opAt 8282 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10966 = true :=
  CycleSubmission.Global.Binding.jumpDest 8263 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8263 ≤ i) (hii : i ≤ 8291) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10966,10967,10969,10970,10973,10974,10975,10976,10978,10979,10980,10982,10983,10984,10986,10987,10990,10991,10993,10994,10995,10996,10997,10998,10999,11000,11001,11002,11003] : List Nat)[i - 8263]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
