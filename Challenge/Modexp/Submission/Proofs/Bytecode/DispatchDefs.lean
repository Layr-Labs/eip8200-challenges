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
  [opAt 396 (.Dup ⟨0, by decide⟩),
   pushAt 397 2 5251,
   opAt 398 .JUMPI,
   pushAt 399 0 0,
   pushAt 400 0 0,
   opAt 401 .RETURN]

def wordEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 396 (.Dup ⟨0, by decide⟩),
   pushAt 397 2 5251,
   opAt 398 .JUMPI,
   opAt 402 .JUMPDEST,
   opAt 403 (.Dup ⟨2, by decide⟩),
   pushAt 404 1 96,
   opAt 405 .ADD,
   opAt 406 (.Dup ⟨2, by decide⟩),
   opAt 407 (.Dup ⟨1, by decide⟩),
   opAt 408 .ADD,
   pushAt 409 1 32,
   opAt 410 (.Dup ⟨3, by decide⟩),
   opAt 411 .GT,
   pushAt 412 1 238,
   opAt 413 .JUMPI,
   pushAt 414 2 1186,
   opAt 415 (.Dup ⟨1, by decide⟩),
   opAt 416 (.Dup ⟨3, by decide⟩),
   pushAt 417 1 96,
   opAt 418 (.Dup ⟨6, by decide⟩),
   opAt 419 (.Dup ⟨8, by decide⟩),
   opAt 420 (.Dup ⟨10, by decide⟩),
   pushAt 421 2 804,
   opAt 422 .JUMP]

def zeroSetupPath := zeroSizePath.take 5
def zeroReturnPath := [opAt 401 .RETURN]
def wordJumpPath := wordEntryPath.take 3
def wordRestPath := wordEntryPath.drop 3
def wordCheckPath := wordRestPath.take 12
def wordTailPath := wordRestPath.drop 12

@[simp] theorem dispatchPCs (i : Nat)
    (hi : 396 ≤ i) (hii : i ≤ 422) :
    Artifact.submissionArtifact.instructionPC i =
      ([562,563,566,567,568,569,570,571,572,574,575,576,577,578,580,581,582,584,585,588,589,590,592,593,594,595,598] : List Nat)[i - 396]! := by
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
    Decode.isValidJumpDest submissionBytecode 570 = true :=
  Artifact.isValidJumpDest_index 402 (by rfl)

set_option maxRecDepth 400000 in
/-- The recogniser's entry, in what the inherited image used as padding. -/
@[simp] theorem jumpMemo :
    Decode.isValidJumpDest submissionBytecode 5251 = true :=
  Artifact.isValidJumpDest_index 4211 (by rfl)

set_option maxRecDepth 400000 in
/-- The appended answer block's entry. -/
@[simp] theorem jumpAnswer :
    Decode.isValidJumpDest submissionBytecode 5428 = true :=
  Artifact.isValidJumpDest_index 4351 (by rfl)

@[simp] theorem jump517 :
    Decode.isValidJumpDest submissionBytecode 135 = true :=
  Artifact.isValidJumpDest_index 78 (by rfl)

set_option maxRecDepth 20000 in
@[simp] theorem jump3000 :
    Decode.isValidJumpDest submissionBytecode 804 = true := by
  have hpc : Artifact.instructionPC 568 = 804 := by decide
  simpa only [hpc] using Artifact.isValidJumpDest_index 568 (by rfl)

def zeroSizeFinalState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 569
    stack := [UInt256.ofNat 0, UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)]
    halt := .Returned
    hReturn := ByteArray.empty }

def zeroSetupState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 569
    stack := [0, 0, UInt256.ofNat 0, UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)] }

def wordDispatchState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 570
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

/-- Entry state of the appended fixed-vector block.  The retargeted jump carries
exactly the stack the pc-570 dispatcher expects, so a miss can restore
`wordDispatchState` by changing nothing but the program counter. -/
def guardEntryState (input : ByteArray) : State :=
  { wordDispatchState input with pc := UInt256.ofNat 5251 }

def wordCheckedState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 585
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
    pc := UInt256.ofNat 135
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
  { wordEntryState input with pc := UInt256.ofNat 804 }

/-- The unchanged dispatcher prefix followed by its retargeted final jump. -/
abbrev WordRouteEnter (input : ByteArray) : Type :=
  Challenge.EvmProof.GasSteps (Main.headerState input)
    (wordRouteEntryState input)

/-- A route miss must restore precisely the already-proved legacy entry. -/
abbrev WordRouteMiss (input : ByteArray) : Type :=
  Challenge.EvmProof.GasSteps (wordRouteEntryState input)
    (wordEntryState input)


end Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
