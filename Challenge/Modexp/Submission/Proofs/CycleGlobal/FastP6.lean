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
  [opAt 7981 .JUMPDEST,
   opAt 7982 (.Dup ⟨0,by decide⟩),
   pushAt 7983 2 10966,
   opAt 7984 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7981 .JUMPDEST,
   opAt 7982 (.Dup ⟨0,by decide⟩),
   pushAt 7983 2 10966,
   opAt 7984 .JUMPI,
   pushAt 7985 0 0,
   opAt 7986 .RETURN]
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
  [opAt 7950 .JUMPDEST,
   pushAt 7951 1 32,
   opAt 7952 .CALLDATALOAD,
   pushAt 7953 2 863,
   opAt 7954 .JUMPI,
   opAt 630 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7950 .JUMPDEST,
   pushAt 7951 1 32,
   opAt 7952 .CALLDATALOAD,
   pushAt 7953 2 863,
   opAt 7954 .JUMPI,
   pushAt 7955 1 64,
   opAt 7956 .CALLDATALOAD,
   opAt 7957 (.Dup ⟨0,by decide⟩),
   pushAt 7958 1 32,
   opAt 7959 .LT,
   pushAt 7960 2 10960,
   opAt 7961 .JUMPI,
   opAt 8260 .JUMPDEST,
   opAt 8261 .POP,
   pushAt 8262 2 863,
   opAt 8263 .JUMP,
   opAt 630 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7950 .JUMPDEST,
   pushAt 7951 1 32,
   opAt 7952 .CALLDATALOAD,
   pushAt 7953 2 863,
   opAt 7954 .JUMPI,
   pushAt 7955 1 64,
   opAt 7956 .CALLDATALOAD,
   opAt 7957 (.Dup ⟨0,by decide⟩),
   pushAt 7958 1 32,
   opAt 7959 .LT,
   pushAt 7960 2 10960,
   opAt 7961 .JUMPI,
   pushAt 7962 0 0,
   opAt 7963 .CALLDATALOAD,
   pushAt 7964 1 96,
   opAt 7965 .ADD,
   opAt 7966 .CALLDATALOAD,
   opAt 7967 (.Dup ⟨1,by decide⟩),
   pushAt 7968 1 32,
   opAt 7969 .SUB,
   pushAt 7970 1 3,
   opAt 7971 .SHL,
   opAt 7972 .SHR,
   pushAt 7973 1 1,
   opAt 7974 .LT,
   pushAt 7975 0 0,
   opAt 7976 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7977 (.Dup ⟨0,by decide⟩),
   opAt 7978 .MSIZE,
   opAt 7979 .SUB,
   opAt 7980 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10526 = true :=
  CycleSubmission.Global.Binding.jumpDest 7950 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10960 = true :=
  CycleSubmission.Global.Binding.jumpDest 8260 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7981 ≤ i) (hii : i ≤ 7986) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10568,10569,10570,10573,10574,10575] : List Nat)[i - 7981]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7950 ≤ i) (hii : i ≤ 7980) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10526,10527,10529,10530,10533,10534,10536,10537,10538,10540,10541,10544,10545,10546,10547,10549,10550,10551,10552,10554,10555,10557,10558,10559,10561,10562,10563,10564,10565,10566,10567] : List Nat)[i - 7950]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7962 ≤ i) (hii : i ≤ 7980) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10545,10546,10547,10549,10550,10551,10552,10554,10555,10557,10558,10559,10561,10562,10563,10564,10565,10566,10567] : List Nat)[i - 7962]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8260 ≤ i) (hii : i ≤ 8263) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10960,10961,10962,10965] : List Nat)[i - 8260]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8264 .JUMPDEST,
   pushAt 8265 1 12,
   opAt 8266 .XOR,
   pushAt 8267 2 10526,
   opAt 8268 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8264 .JUMPDEST,
   pushAt 8265 1 12,
   opAt 8266 .XOR,
   pushAt 8267 2 10526,
   opAt 8268 .JUMPI,
   pushAt 8269 0 0,
   opAt 8270 .CALLDATALOAD,
   pushAt 8271 1 32,
   opAt 8272 .CALLDATALOAD,
   opAt 8273 .ADD,
   pushAt 8274 1 96,
   opAt 8275 .ADD,
   opAt 8276 .CALLDATALOAD,
   pushAt 8277 1 160,
   opAt 8278 .SHR,
   pushAt 8279 2 863,
   opAt 8280 .JUMPI,
   opAt 630 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8264 .JUMPDEST,
   pushAt 8265 1 12,
   opAt 8266 .XOR,
   pushAt 8267 2 10526,
   opAt 8268 .JUMPI,
   pushAt 8269 0 0,
   opAt 8270 .CALLDATALOAD,
   pushAt 8271 1 32,
   opAt 8272 .CALLDATALOAD,
   opAt 8273 .ADD,
   pushAt 8274 1 96,
   opAt 8275 .ADD,
   opAt 8276 .CALLDATALOAD,
   pushAt 8277 1 160,
   opAt 8278 .SHR,
   pushAt 8279 2 863,
   opAt 8280 .JUMPI,
   pushAt 8281 1 12,
   pushAt 8282 0 0,
   opAt 8283 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10966 = true :=
  CycleSubmission.Global.Binding.jumpDest 8264 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8264 ≤ i) (hii : i ≤ 8292) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10966,10967,10969,10970,10973,10974,10975,10976,10978,10979,10980,10982,10983,10984,10986,10987,10990,10991,10993,10994,10995,10996,10997,10998,10999,11000,11001,11002,11003] : List Nat)[i - 8264]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
