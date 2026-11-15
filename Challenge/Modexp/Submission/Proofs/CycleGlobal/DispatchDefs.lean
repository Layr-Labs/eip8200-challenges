import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Main
open CycleSubmission.SharedStackArgs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# MODEXP output dispatcher

The zero-width EIP-198 result is a complete terminating bytecode path.  It is
kept separate because it touches no operand bytes or memory and therefore has
the challenge's minimum gas cost.
-/
namespace CycleSubmission.Global.Dispatch
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics
open EvmSemantics.EVM
def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode,hplain,havailable⟩
def opAt (index : Nat) (op : Operation)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index,.op op,hget,wfOp hopcode hplain havailable⟩
def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index,.push width value,hget,hwf⟩
def zeroSizePath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 360 (.Dup ⟨0,by decide⟩),
   pushAt 361 2 500,
   opAt 362 .JUMPI,
   pushAt 363 0 0,
   pushAt 364 0 0,
   opAt 365 .RETURN]
def wordEntryPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 360 (.Dup ⟨0,by decide⟩),
   pushAt 361 2 500,
   opAt 362 .JUMPI,
   opAt 366 .JUMPDEST,
   opAt 367 (.Dup ⟨2,by decide⟩),
   pushAt 368 1 96,
   opAt 369 .ADD,
   opAt 370 (.Dup ⟨2,by decide⟩),
   opAt 371 (.Dup ⟨1,by decide⟩),
   opAt 372 .ADD,
   pushAt 373 1 32,
   opAt 374 (.Dup ⟨3,by decide⟩),
   opAt 375 .GT,
   pushAt 376 1 172,
   opAt 377 .JUMPI,
   pushAt 378 2 1186,
   opAt 379 (.Dup ⟨1,by decide⟩),
   opAt 380 (.Dup ⟨3,by decide⟩),
   pushAt 381 1 96,
   opAt 382 (.Dup ⟨6,by decide⟩),
   opAt 383 (.Dup ⟨8,by decide⟩),
   opAt 384 (.Dup ⟨10,by decide⟩),
   pushAt 385 1 96,
   opAt 386 .JUMP]
def zeroSetupPath := zeroSizePath.take 5
def zeroReturnPath := [opAt 365 .RETURN]
def wordJumpPath := wordEntryPath.take 3
def wordRestPath := wordEntryPath.drop 3
def wordCheckPath := wordRestPath.take 12
def wordTailPath := wordRestPath.drop 12
@[simp] theorem dispatchPCs (i : Nat) (hi : 360 ≤ i) (hii : i ≤ 386) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([492,493,496,497,498,499,500,501,502,504,505,506,507,508,510,511,512,514,515,518,519,520,522,523,524,525,527] : List Nat)[i - 360]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl
@[simp] theorem activeWordsAfterUInt256_zero (s : State) (offset : Nat) :
    s.activeWordsAfterUInt256 offset 0 = UInt256.ofNat s.activeWords.toNat := by
  simp [State.activeWordsAfterUInt256,MachineState.activeWordsAfter]
@[simp] theorem readPadded_empty_zero (start : Nat) :
    MachineState.readPadded ByteArray.empty start 0 = ByteArray.empty := by
  apply ByteArray.ext
  simp [MachineState.readPadded]
@[simp] theorem jump1237 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 500 = true :=
  CycleSubmission.Global.Binding.jumpDest 366 (by rfl)
@[simp] theorem jump517 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 96 = true :=
  CycleSubmission.Global.Binding.jumpDest 67 (by rfl)
def zeroSizeFinalState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 499
    stack := [UInt256.ofNat 0,UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)]
    halt := .Returned
    hReturn := ByteArray.empty }
def zeroSetupState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 499
    stack := [0,0,UInt256.ofNat 0,UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)] }
def wordDispatchState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 500
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input),UInt256.ofNat (baseSize input)] }
def wordCheckedState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 515
    stack := [UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input),UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input),UInt256.ofNat (baseSize input)] }
/-- Calling-convention state at the first instruction of `modexpWord`. -/
def wordEntryState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 96
    stack := [UInt256.ofNat b,UInt256.ofNat e,UInt256.ofNat m,
      UInt256.ofNat 96,UInt256.ofNat expOff,UInt256.ofNat modOff,
      UInt256.ofNat 1186,UInt256.ofNat modOff,UInt256.ofNat expOff,
      UInt256.ofNat m,UInt256.ofNat e,UInt256.ofNat b] }
/-- The one-word dispatcher prefix, ending at the word entry. -/
abbrev WordRouteEnter (input : ByteArray) : Type :=
  Challenge.EvmProof.GasSteps (Main.headerState input)
    (wordEntryState input)
end CycleSubmission.Global.Dispatch
