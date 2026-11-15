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
/-- The empty-modulus test at pc 3470 (instructions 511..513, in the former unreachable
filler behind the memo hit exit) for a nonzero `msize`: `JUMPDEST PUSH2 3425 JUMPI`
consumes `msize` and lands on the zero-exponent test appended at pc 3425 with an
empty stack. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7804 .JUMPDEST,
   opAt 7805 (.Dup ⟨0,by decide⟩),
   pushAt 7806 2 10966,
   opAt 7807 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7804 .JUMPDEST,
   opAt 7805 (.Dup ⟨0,by decide⟩),
   pushAt 7806 2 10966,
   opAt 7807 .JUMPI,
   pushAt 7808 0 0,
   opAt 7809 .RETURN]
/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/
/-- The zero-exponent test appended at pc 3425 (instructions 8638..8642) for a nonzero
`esize`: `JUMPDEST PUSH1 32 CALLDATALOAD PUSH2 698 JUMPI` lands on the `JUMPDEST` at
pc 698 (instruction 488), which falls into the fixed-vector recogniser at pc 699 with an
empty stack. -/
def blkZeroExpMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7773 .JUMPDEST,
   pushAt 7774 1 32,
   opAt 7775 .CALLDATALOAD,
   pushAt 7776 2 894,
   opAt 7777 .JUMPI,
   opAt 629 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7773 .JUMPDEST,
   pushAt 7774 1 32,
   opAt 7775 .CALLDATALOAD,
   pushAt 7776 2 894,
   opAt 7777 .JUMPI,
   pushAt 7778 1 64,
   opAt 7779 .CALLDATALOAD,
   opAt 7780 (.Dup ⟨0,by decide⟩),
   pushAt 7781 1 32,
   opAt 7782 .LT,
   pushAt 7783 2 10960,
   opAt 7784 .JUMPI,
   opAt 8260 .JUMPDEST,
   opAt 8261 .POP,
   pushAt 8262 2 894,
   opAt 8263 .JUMP,
   opAt 629 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7773 .JUMPDEST,
   pushAt 7774 1 32,
   opAt 7775 .CALLDATALOAD,
   pushAt 7776 2 894,
   opAt 7777 .JUMPI,
   pushAt 7778 1 64,
   opAt 7779 .CALLDATALOAD,
   opAt 7780 (.Dup ⟨0,by decide⟩),
   pushAt 7781 1 32,
   opAt 7782 .LT,
   pushAt 7783 2 10960,
   opAt 7784 .JUMPI,
   pushAt 7785 0 0,
   opAt 7786 .CALLDATALOAD,
   pushAt 7787 1 96,
   opAt 7788 .ADD,
   opAt 7789 .CALLDATALOAD,
   opAt 7790 (.Dup ⟨1,by decide⟩),
   pushAt 7791 1 32,
   opAt 7792 .SUB,
   pushAt 7793 1 3,
   opAt 7794 .SHL,
   opAt 7795 .SHR,
   pushAt 7796 1 1,
   opAt 7797 .LT,
   pushAt 7798 0 0,
   opAt 7799 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 7800 (.Dup ⟨0,by decide⟩),
   opAt 7801 .MSIZE,
   opAt 7802 .SUB,
   opAt 7803 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10280 = true :=
  CycleSubmission.Global.Binding.jumpDest 7773 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10960 = true :=
  CycleSubmission.Global.Binding.jumpDest 8260 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 7804 ≤ i) (hii : i ≤ 7809) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10322,10323,10324,10327,10328,10329] : List Nat)[i - 7804]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 7773 ≤ i) (hii : i ≤ 7803) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10280,10281,10283,10284,10287,10288,10290,10291,10292,10294,10295,10298,10299,10300,10301,10303,10304,10305,10306,10308,10309,10311,10312,10313,10315,10316,10317,10318,10319,10320,10321] : List Nat)[i - 7773]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 7785 ≤ i) (hii : i ≤ 7803) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10299,10300,10301,10303,10304,10305,10306,10308,10309,10311,10312,10313,10315,10316,10317,10318,10319,10320,10321] : List Nat)[i - 7785]! := by
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
   pushAt 8267 2 10280,
   opAt 8268 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8264 .JUMPDEST,
   pushAt 8265 1 12,
   opAt 8266 .XOR,
   pushAt 8267 2 10280,
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
   pushAt 8279 2 894,
   opAt 8280 .JUMPI,
   opAt 629 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8264 .JUMPDEST,
   pushAt 8265 1 12,
   opAt 8266 .XOR,
   pushAt 8267 2 10280,
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
   pushAt 8279 2 894,
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
