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
/-- The empty-modulus test at pc 3350 (instructions 511..513, in the former unreachable
filler behind the memo hit exit) for a nonzero `msize`: `JUMPDEST PUSH2 3305 JUMPI`
consumes `msize` and lands on the zero-exponent test appended at pc 3305 with an
empty stack. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7978 .JUMPDEST,
   opAt 7979 (.Dup ⟨0,by decide⟩),
   pushAt 7980 2 10962,
   opAt 7981 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7978 .JUMPDEST,
   opAt 7979 (.Dup ⟨0,by decide⟩),
   pushAt 7980 2 10962,
   opAt 7981 .JUMPI,
   pushAt 7982 0 0,
   opAt 7983 .RETURN]
/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/
/-- The zero-exponent test appended at pc 3305 (instructions 8638..8642) for a nonzero
`esize`: `JUMPDEST PUSH1 32 CALLDATALOAD PUSH2 698 JUMPI` lands on the `JUMPDEST` at
pc 698 (instruction 488), which falls into the fixed-vector recogniser at pc 699 with an
empty stack. -/
def blkZeroExpMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7947 .JUMPDEST,
   pushAt 7948 1 32,
   opAt 7949 .CALLDATALOAD,
   pushAt 7950 2 1109,
   opAt 7951 .JUMPI,
   opAt 807 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7947 .JUMPDEST,
   pushAt 7948 1 32,
   opAt 7949 .CALLDATALOAD,
   pushAt 7950 2 1109,
   opAt 7951 .JUMPI,
   pushAt 7952 1 64,
   opAt 7953 .CALLDATALOAD,
   opAt 7954 (.Dup ⟨0,by decide⟩),
   pushAt 7955 1 32,
   opAt 7956 .LT,
   pushAt 7957 2 10956,
   opAt 7958 .JUMPI,
   opAt 8258 .JUMPDEST,
   opAt 8259 .POP,
   pushAt 8260 2 1109,
   opAt 8261 .JUMP,
   opAt 807 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7947 .JUMPDEST,
   pushAt 7948 1 32,
   opAt 7949 .CALLDATALOAD,
   pushAt 7950 2 1109,
   opAt 7951 .JUMPI,
   pushAt 7952 1 64,
   opAt 7953 .CALLDATALOAD,
   opAt 7954 (.Dup ⟨0,by decide⟩),
   pushAt 7955 1 32,
   opAt 7956 .LT,
   pushAt 7957 2 10956,
   opAt 7958 .JUMPI,
   pushAt 7959 0 0,
   opAt 7960 .CALLDATALOAD,
   pushAt 7961 1 96,
   opAt 7962 .ADD,
   opAt 7963 .CALLDATALOAD,
   opAt 7964 (.Dup ⟨1,by decide⟩),
   pushAt 7965 1 32,
   opAt 7966 .SUB,
   pushAt 7967 1 3,
   opAt 7968 .SHL,
   opAt 7969 .SHR,
   pushAt 7970 1 1,
   opAt 7971 .LT,
   pushAt 7972 0 0,
   opAt 7973 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7974 (.Dup ⟨0,by decide⟩),
   opAt 7975 .MSIZE,
   opAt 7976 .SUB,
   opAt 7977 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10521 = true :=
  CycleSubmission.Global.Binding.jumpDest 7947 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10956 = true :=
  CycleSubmission.Global.Binding.jumpDest 8258 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7978 ≤ i) (hii : i ≤ 7983) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10563,10564,10565,10568,10569,10570] : List Nat)[i - 7978]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7947 ≤ i) (hii : i ≤ 7977) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10521,10522,10524,10525,10528,10529,10531,10532,10533,10535,10536,10539,10540,10541,10542,10544,10545,10546,10547,10549,10550,10552,10553,10554,10556,10557,10558,10559,10560,10561,10562] : List Nat)[i - 7947]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7959 ≤ i) (hii : i ≤ 7977) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10540,10541,10542,10544,10545,10546,10547,10549,10550,10552,10553,10554,10556,10557,10558,10559,10560,10561,10562] : List Nat)[i - 7959]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8258 ≤ i) (hii : i ≤ 8261) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10956,10957,10958,10961] : List Nat)[i - 8258]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8262 .JUMPDEST,
   pushAt 8263 1 12,
   opAt 8264 .XOR,
   pushAt 8265 2 10521,
   opAt 8266 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8262 .JUMPDEST,
   pushAt 8263 1 12,
   opAt 8264 .XOR,
   pushAt 8265 2 10521,
   opAt 8266 .JUMPI,
   pushAt 8267 0 0,
   opAt 8268 .CALLDATALOAD,
   pushAt 8269 1 32,
   opAt 8270 .CALLDATALOAD,
   opAt 8271 .ADD,
   pushAt 8272 1 96,
   opAt 8273 .ADD,
   opAt 8274 .CALLDATALOAD,
   pushAt 8275 1 160,
   opAt 8276 .SHR,
   pushAt 8277 2 1109,
   opAt 8278 .JUMPI,
   opAt 807 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8262 .JUMPDEST,
   pushAt 8263 1 12,
   opAt 8264 .XOR,
   pushAt 8265 2 10521,
   opAt 8266 .JUMPI,
   pushAt 8267 0 0,
   opAt 8268 .CALLDATALOAD,
   pushAt 8269 1 32,
   opAt 8270 .CALLDATALOAD,
   opAt 8271 .ADD,
   pushAt 8272 1 96,
   opAt 8273 .ADD,
   opAt 8274 .CALLDATALOAD,
   pushAt 8275 1 160,
   opAt 8276 .SHR,
   pushAt 8277 2 1109,
   opAt 8278 .JUMPI,
   pushAt 8279 1 12,
   pushAt 8280 0 0,
   opAt 8281 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10962 = true :=
  CycleSubmission.Global.Binding.jumpDest 8262 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8262 ≤ i) (hii : i ≤ 8294) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10962,10963,10965,10966,10969,10970,10971,10972,10974,10975,10976,10978,10979,10980,10982,10983,10986,10987,10989,10990,10991,10992,10993,10994,10995,10996,10997,10998,10999,11000,11001,11002,11003] : List Nat)[i - 8262]! := by
 interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
end CycleSubmission.Global.Fast
