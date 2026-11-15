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
/-- The empty-modulus test at pc 1470 (instructions 511..513, in the former unreachable
filler behind the memo hit exit) for a nonzero `msize`: `JUMPDEST PUSH2 1425 JUMPI`
consumes `msize` and lands on the zero-exponent test appended at pc 1425 with an
empty stack. -/
def blk1341 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8196 .JUMPDEST,
   opAt 8197 (.Dup ⟨0,by decide⟩),
   pushAt 8198 2 10962,
   opAt 8199 .JUMPI]
/-- The same test for `msize = 0`: the `JUMPI` falls through to `PUSH0 PUSH0 RETURN`
(instructions 514..516, pc 3487..3489), which returns the empty byte array. -/
def blkEmptyModulus :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8196 .JUMPDEST,
   opAt 8197 (.Dup ⟨0,by decide⟩),
   pushAt 8198 2 10962,
   opAt 8199 .JUMPI,
   pushAt 8200 0 0,
   opAt 8201 .RETURN]
/- `blk1345` (the oversize bail target `BAIL3`, pristine instructions 1345..1350) is
deleted with the size test that was its only predecessor: nothing jumps to it any more,
so the bytes are not in the candidate and the block, `bail3State`, `run_sizeCheck_bail`,
`run_bail3` and their two gas traces in `Fast/Setup.lean` are dead proof code. -/
/-- The zero-exponent test appended at pc 1425 (instructions 8638..8642) for a nonzero
`esize`: `JUMPDEST PUSH1 32 CALLDATALOAD PUSH2 698 JUMPI` lands on the `JUMPDEST` at
pc 698 (instruction 488), which falls into the fixed-vector recogniser at pc 699 with an
empty stack. -/
def blkZeroExpMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8165 .JUMPDEST,
   pushAt 8166 1 32,
   opAt 8167 .CALLDATALOAD,
   pushAt 8168 2 1154,
   opAt 8169 .JUMPI,
   opAt 841 .JUMPDEST]
def blkZeroExpWide :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8165 .JUMPDEST,
   pushAt 8166 1 32,
   opAt 8167 .CALLDATALOAD,
   pushAt 8168 2 1154,
   opAt 8169 .JUMPI,
   pushAt 8170 1 64,
   opAt 8171 .CALLDATALOAD,
   opAt 8172 (.Dup ⟨0,by decide⟩),
   pushAt 8173 1 32,
   opAt 8174 .LT,
   pushAt 8175 2 10956,
   opAt 8176 .JUMPI,
   opAt 8262 .JUMPDEST,
   opAt 8263 .POP,
   pushAt 8264 2 1154,
   opAt 8265 .JUMP,
   opAt 841 .JUMPDEST]
def blkZeroExpHit :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8165 .JUMPDEST,
   pushAt 8166 1 32,
   opAt 8167 .CALLDATALOAD,
   pushAt 8168 2 1154,
   opAt 8169 .JUMPI,
   pushAt 8170 1 64,
   opAt 8171 .CALLDATALOAD,
   opAt 8172 (.Dup ⟨0,by decide⟩),
   pushAt 8173 1 32,
   opAt 8174 .LT,
   pushAt 8175 2 10956,
   opAt 8176 .JUMPI,
   pushAt 8177 0 0,
   opAt 8178 .CALLDATALOAD,
   pushAt 8179 1 96,
   opAt 8180 .ADD,
   opAt 8181 .CALLDATALOAD,
   opAt 8182 (.Dup ⟨1,by decide⟩),
   pushAt 8183 1 32,
   opAt 8184 .SUB,
   pushAt 8185 1 3,
   opAt 8186 .SHL,
   opAt 8187 .SHR,
   pushAt 8188 1 1,
   opAt 8189 .LT,
   pushAt 8190 0 0,
   opAt 8191 .MSTORE]
def blkZeroExpReturn :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8192 (.Dup ⟨0,by decide⟩),
   opAt 8193 .MSIZE,
   opAt 8194 .SUB,
   opAt 8195 .RETURN]
theorem jumpDestZeroExp : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10834 = true :=
  CycleSubmission.Global.Binding.jumpDest 8165 (by rfl)
theorem jumpDestZeroExpCleanup : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10956 = true :=
  CycleSubmission.Global.Binding.jumpDest 8262 (by rfl)
@[simp] theorem packedEmptyPCs (i : Nat) (hi : 8196 ≤ i) (hii : i ≤ 8201) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10876,10877,10878,10881,10882,10883] : List Nat)[i - 8196]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedHeadPCs (i : Nat) (hi : 8165 ≤ i) (hii : i ≤ 8195) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10834,10835,10837,10838,10841,10842,10844,10845,10846,10848,10849,10852,10853,10854,10855,10857,10858,10859,10860,10862,10863,10865,10866,10867,10869,10870,10871,10872,10873,10874,10875] : List Nat)[i - 8165]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem packedTailPCs (i : Nat) (hi : 8177 ≤ i) (hii : i ≤ 8195) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10853,10854,10855,10857,10858,10859,10860,10862,10863,10865,10866,10867,10869,10870,10871,10872,10873,10874,10875] : List Nat)[i - 8177]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
@[simp] theorem zeroExpCleanupPCs (i : Nat) (hi : 8262 ≤ i) (hii : i ≤ 8265) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10956,10957,10958,10961] : List Nat)[i - 8262]! := by
  interval_cases i <;> rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] <;> rfl
def blkZero12WidthMiss :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8266 .JUMPDEST,
   pushAt 8267 1 12,
   opAt 8268 .XOR,
   pushAt 8269 2 10834,
   opAt 8270 .JUMPI]
def blkZero12Nonzero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8266 .JUMPDEST,
   pushAt 8267 1 12,
   opAt 8268 .XOR,
   pushAt 8269 2 10834,
   opAt 8270 .JUMPI,
   pushAt 8271 0 0,
   opAt 8272 .CALLDATALOAD,
   pushAt 8273 1 32,
   opAt 8274 .CALLDATALOAD,
   opAt 8275 .ADD,
   pushAt 8276 1 96,
   opAt 8277 .ADD,
   opAt 8278 .CALLDATALOAD,
   pushAt 8279 1 160,
   opAt 8280 .SHR,
   pushAt 8281 2 1154,
   opAt 8282 .JUMPI,
   opAt 841 .JUMPDEST]
def blkZero12Zero :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8266 .JUMPDEST,
   pushAt 8267 1 12,
   opAt 8268 .XOR,
   pushAt 8269 2 10834,
   opAt 8270 .JUMPI,
   pushAt 8271 0 0,
   opAt 8272 .CALLDATALOAD,
   pushAt 8273 1 32,
   opAt 8274 .CALLDATALOAD,
   opAt 8275 .ADD,
   pushAt 8276 1 96,
   opAt 8277 .ADD,
   opAt 8278 .CALLDATALOAD,
   pushAt 8279 1 160,
   opAt 8280 .SHR,
   pushAt 8281 2 1154,
   opAt 8282 .JUMPI,
   pushAt 8283 1 12,
   pushAt 8284 0 0,
   opAt 8285 .RETURN]
theorem jumpDestZero12 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10962 = true :=
  CycleSubmission.Global.Binding.jumpDest 8266 (by rfl)
@[simp] theorem packedZero12PCs (i : Nat) (hi : 8266 ≤ i) (hii : i ≤ 8293) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10962,10963,10965,10966,10969,10970,10971,10972,10974,10975,10976,10978,10979,10980,10982,10983,10986,10987,10989,10990,10991,10992,10993,10994,10995,10996,10997,10998] : List Nat)[i - 8266]! := by
  interval_cases i <;>
    exact CycleSubmission.PCCertificate.selectedPC _ (by decide)
@[simp] theorem packedZero12PCs_part1 (i : Nat) (hi : 8298 ≤ i) (hii : i ≤ 8298) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([11003] : List Nat)[i - 8298]! := by
  interval_cases i
  exact CycleSubmission.PCCertificate.selectedPC _ (by decide)
end CycleSubmission.Global.Fast
