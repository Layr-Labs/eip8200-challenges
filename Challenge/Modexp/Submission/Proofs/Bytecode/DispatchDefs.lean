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
  [opAt 921 .JUMPDEST, opAt 922 (.Dup ⟨0, by decide⟩),
   pushAt 923 2 1237, opAt 924 .JUMPI,
   pushAt 925 0 0, pushAt 926 0 0, opAt 927 .RETURN]

def wordEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 921 .JUMPDEST, opAt 922 (.Dup ⟨0, by decide⟩),
   pushAt 923 2 1237, opAt 924 .JUMPI,
   opAt 928 .JUMPDEST, opAt 929 (.Dup ⟨2, by decide⟩),
   pushAt 930 1 96, opAt 931 .ADD,
   opAt 932 (.Dup ⟨2, by decide⟩), opAt 933 (.Dup ⟨1, by decide⟩),
   opAt 934 .ADD, pushAt 935 1 32, opAt 936 (.Dup ⟨3, by decide⟩),
   opAt 937 .GT, pushAt 938 2 1268, opAt 939 .JUMPI,
   pushAt 940 2 1267, opAt 941 (.Dup ⟨1, by decide⟩),
   opAt 942 (.Dup ⟨3, by decide⟩), pushAt 943 1 96,
   opAt 944 (.Dup ⟨6, by decide⟩), opAt 945 (.Dup ⟨8, by decide⟩),
   opAt 946 (.Dup ⟨10, by decide⟩), pushAt 947 2 3000, opAt 948 .JUMP]

def zeroSetupPath := zeroSizePath.take 6
def zeroReturnPath := [opAt 927 .RETURN]
def wordJumpPath := wordEntryPath.take 4
def wordRestPath := wordEntryPath.drop 4
def wordCheckPath := wordRestPath.take 12
def wordTailPath := wordRestPath.drop 12

@[simp] theorem dispatchPCs (i : Nat) (hi : 921 ≤ i) (hii : i ≤ 948) :
    Artifact.submissionArtifact.instructionPC i =
      [1228,1229,1230,1233,1234,1235,1236,1237,1238,1239,1241,1242,
       1243,1244,1245,1247,1248,1249,1252,1253,1256,1257,1258,1260,
       1261,1262,1263,1266][i - 921]! := by
  interval_cases i <;> decide

@[simp] theorem activeWordsAfterUInt256_zero (s : State) (offset : Nat) :
    s.activeWordsAfterUInt256 offset 0 = UInt256.ofNat s.activeWords.toNat := by
  simp [State.activeWordsAfterUInt256, MachineState.activeWordsAfter]

@[simp] theorem readPadded_empty_zero (start : Nat) :
    MachineState.readPadded ByteArray.empty start 0 = ByteArray.empty := by
  apply ByteArray.ext
  simp [MachineState.readPadded]

@[simp] theorem jump1237 :
    Decode.isValidJumpDest submissionBytecode 1237 = true :=
  Artifact.isValidJumpDest_index 928 (by rfl)

@[simp] theorem jump517 :
    Decode.isValidJumpDest submissionBytecode 517 = true :=
  Artifact.isValidJumpDest_index 415 (by rfl)

@[simp] theorem jump3000 :
    Decode.isValidJumpDest submissionBytecode 3000 = true :=
  Artifact.isValidJumpDest_index 1831 (by rfl)

def zeroSizeFinalState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1236
    stack := [UInt256.ofNat 0, UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)]
    halt := .Returned
    hReturn := ByteArray.empty }

def zeroSetupState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1236
    stack := [0, 0, UInt256.ofNat 0, UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)] }

def wordDispatchState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1237
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def wordCheckedState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1253
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
    pc := UInt256.ofNat 517
    stack := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat 96, UInt256.ofNat expOff, UInt256.ofNat modOff,
      UInt256.ofNat 1267, UInt256.ofNat modOff, UInt256.ofNat expOff,
      UInt256.ofNat m, UInt256.ofNat e, UInt256.ofNat b] }

/-! ## Retargeted one-word dispatch boundary

The fixed-width successor changes only the destination pushed by the final
instruction pair of the one-word dispatcher.  Keep that changed boundary
separate from `wordEntryState`: a route miss later restores the exact legacy
pc-517 state consumed by the existing word implementation.

These aliases deliberately state only the composition interface.  The exact
located-instruction witnesses belong to the route execution module after the
submission artifact has been regenerated.
-/

/-- State reached by the retargeted one-word dispatcher at the appended route. -/
def wordRouteEntryState (input : ByteArray) : State :=
  { wordEntryState input with pc := UInt256.ofNat 3000 }

/-- The unchanged dispatcher prefix followed by its retargeted final jump. -/
abbrev WordRouteEnter (input : ByteArray) : Type :=
  Challenge.EvmProof.GasSteps (Main.headerState input)
    (wordRouteEntryState input)

/-- A route miss must restore precisely the already-proved legacy entry. -/
abbrev WordRouteMiss (input : ByteArray) : Type :=
  Challenge.EvmProof.GasSteps (wordRouteEntryState input)
    (wordEntryState input)


end Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

