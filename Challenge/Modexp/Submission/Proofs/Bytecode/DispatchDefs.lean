import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Main
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# MODEXP output dispatcher

The zero-width EIP-198 result is a complete terminating bytecode path.  It is
kept separate because it touches no operand bytes or memory and therefore has
the challenge's minimum gas cost.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

open EvmSemantics
open EvmSemantics.EVM

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def zeroSizePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 394 (.Dup ⟨0, by decide⟩),
   pushAt 395 2 568,
   opAt 396 .JUMPI,
   pushAt 397 0 0,
   pushAt 398 0 0,
   opAt 399 .RETURN]

def wordEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 394 (.Dup ⟨0, by decide⟩),
   pushAt 395 2 568,
   opAt 396 .JUMPI,
   opAt 400 .JUMPDEST,
   opAt 401 (.Dup ⟨2, by decide⟩),
   pushAt 402 1 96,
   opAt 403 .ADD,
   opAt 404 (.Dup ⟨2, by decide⟩),
   opAt 405 (.Dup ⟨1, by decide⟩),
   opAt 406 .ADD,
   pushAt 407 1 32,
   opAt 408 (.Dup ⟨3, by decide⟩),
   opAt 409 .GT,
   pushAt 410 1 236,
   opAt 411 .JUMPI,
   pushAt 412 2 1186,
   opAt 413 (.Dup ⟨1, by decide⟩),
   opAt 414 (.Dup ⟨3, by decide⟩),
   pushAt 415 1 96,
   opAt 416 (.Dup ⟨6, by decide⟩),
   opAt 417 (.Dup ⟨8, by decide⟩),
   opAt 418 (.Dup ⟨10, by decide⟩),
   pushAt 419 2 1634,
   opAt 420 .JUMP]

def zeroSetupPath := zeroSizePath.take 5
def zeroReturnPath := [opAt 399 .RETURN]
def wordJumpPath := wordEntryPath.take 3
def wordRestPath := wordEntryPath.drop 3
def wordCheckPath := wordRestPath.take 12
def wordTailPath := wordRestPath.drop 12

@[simp] theorem dispatchPCs (i : Nat)
    (hi : 394 ≤ i) (hii : i ≤ 420) :
    Artifact.submissionArtifact.instructionPC i =
      ([560,561,564,565,566,567,568,569,570,572,573,574,575,576,578,579,580,582,583,586,587,588,590,591,592,593,596] : List Nat)[i - 394]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem activeWordsAfterUInt256_zero (s : State) (offset : Nat) :
    s.activeWordsAfterUInt256 offset 0 = UInt256.ofNat s.activeWords.toNat := by
  simp [State.activeWordsAfterUInt256, MachineState.activeWordsAfter]

@[simp] theorem readPadded_empty_zero (start : Nat) :
    MachineState.readPadded ByteArray.empty start 0 = ByteArray.empty := by
  apply ByteArray.ext
  simp [MachineState.readPadded]

@[simp] theorem jump1237 :
    Decode.isValidJumpDest submissionBytecode 568 = true :=
  Artifact.isValidJumpDest_index 400 (by rfl)

@[simp] theorem jump517 :
    Decode.isValidJumpDest submissionBytecode 133 = true :=
  Artifact.isValidJumpDest_index 76 (by rfl)

set_option maxRecDepth 20000 in
@[simp] theorem jump3000 :
    Decode.isValidJumpDest submissionBytecode 1634 = true := by
  have hpc : Artifact.instructionPC 1160 = 1634 := by decide
  simpa only [hpc] using Artifact.isValidJumpDest_index 1160 (by rfl)

def zeroSizeFinalState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 567
    stack := [UInt256.ofNat 0, UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)]
    halt := .Returned
    hReturn := ByteArray.empty }

def zeroSetupState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 567
    stack := [0, 0, UInt256.ofNat 0, UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)] }

def wordDispatchState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 568
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def wordCheckedState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 583
    stack := [UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

/-- Calling-convention state at the first instruction of `modexpWord`. -/
def wordEntryState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 133
    stack := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat 96, UInt256.ofNat expOff, UInt256.ofNat modOff,
      UInt256.ofNat 1186, UInt256.ofNat modOff, UInt256.ofNat expOff,
      UInt256.ofNat m, UInt256.ofNat e, UInt256.ofNat b] }

/-! ## Retargeted one-word dispatch boundary

The fixed-width successor changes only the destination pushed by the final
instruction pair of the one-word dispatcher.  Keep that changed boundary
separate from `wordEntryState`: a route miss later restores the exact legacy
pc-599 state consumed by the existing word implementation.

These aliases deliberately state only the composition interface.  The exact
located-instruction witnesses belong to the route execution module after the
submission artifact has been regenerated.
-/

/-- State reached by the retargeted one-word dispatcher at the appended route. -/
def wordRouteEntryState (input : ByteArray) : State :=
  { wordEntryState input with pc := UInt256.ofNat 1634 }

/-- The unchanged dispatcher prefix followed by its retargeted final jump. -/
abbrev WordRouteEnter (input : ByteArray) : Type :=
  Challenge.EvmProof.GasSteps (Main.headerState input)
    (wordRouteEntryState input)

/-- A route miss must restore precisely the already-proved legacy entry. -/
abbrev WordRouteMiss (input : ByteArray) : Type :=
  Challenge.EvmProof.GasSteps (wordRouteEntryState input)
    (wordEntryState input)


end Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
