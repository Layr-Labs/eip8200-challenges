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
  [opAt 855 .JUMPDEST, opAt 856 (.Dup ⟨0, by decide⟩),
   pushAt 857 2 1122, opAt 858 .JUMPI,
   pushAt 859 0 0, pushAt 860 0 0, opAt 861 .RETURN]

def wordEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 855 .JUMPDEST, opAt 856 (.Dup ⟨0, by decide⟩),
   pushAt 857 2 1122, opAt 858 .JUMPI,
   opAt 862 .JUMPDEST, opAt 863 (.Dup ⟨2, by decide⟩),
   pushAt 864 1 96, opAt 865 .ADD,
   opAt 866 (.Dup ⟨2, by decide⟩), opAt 867 (.Dup ⟨1, by decide⟩),
   opAt 868 .ADD, pushAt 869 1 32, opAt 870 (.Dup ⟨3, by decide⟩),
   opAt 871 .GT, pushAt 872 2 1152, opAt 873 .JUMPI,
   pushAt 874 2 1186, opAt 875 (.Dup ⟨1, by decide⟩),
   opAt 876 (.Dup ⟨3, by decide⟩), pushAt 877 1 96,
   opAt 878 (.Dup ⟨6, by decide⟩), opAt 879 (.Dup ⟨8, by decide⟩),
   opAt 880 (.Dup ⟨10, by decide⟩), pushAt 881 2 2042, opAt 882 .JUMP]

def zeroSetupPath := zeroSizePath.take 6
def zeroReturnPath := [opAt 861 .RETURN]
def wordJumpPath := wordEntryPath.take 4
def wordRestPath := wordEntryPath.drop 4
def wordCheckPath := wordRestPath.take 12
def wordTailPath := wordRestPath.drop 12

@[simp] theorem dispatchPCs (i : Nat)
    (hi : 855 ≤ i) (hii : i ≤ 882) :
    Artifact.submissionArtifact.instructionPC i =
      ([1113,1114,1115,1118,1119,1120,1121,1122,1123,1124,1126,1127,1128,1129,1130,1132,1133,1134,1137,1138,1141,1142,1143,1145,1146,1147,1148,1151] : List Nat)[i - 855]! := by
  interval_cases i <;> decide

@[simp] theorem activeWordsAfterUInt256_zero (s : State) (offset : Nat) :
    s.activeWordsAfterUInt256 offset 0 = UInt256.ofNat s.activeWords.toNat := by
  simp [State.activeWordsAfterUInt256, MachineState.activeWordsAfter]

@[simp] theorem readPadded_empty_zero (start : Nat) :
    MachineState.readPadded ByteArray.empty start 0 = ByteArray.empty := by
  apply ByteArray.ext
  simp [MachineState.readPadded]

@[simp] theorem jump1237 :
    Decode.isValidJumpDest submissionBytecode 1122 = true :=
  Artifact.isValidJumpDest_index 862 (by rfl)

@[simp] theorem jump517 :
    Decode.isValidJumpDest submissionBytecode 517 = true :=
  Artifact.isValidJumpDest_index 430 (by rfl)

set_option maxRecDepth 20000 in
@[simp] theorem jump3000 :
    Decode.isValidJumpDest submissionBytecode 2042 = true := by
  have hpc : Artifact.instructionPC 1508 = 2042 := by decide
  simpa only [hpc] using Artifact.isValidJumpDest_index 1508 (by rfl)

def zeroSizeFinalState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1121
    stack := [UInt256.ofNat 0, UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)]
    halt := .Returned
    hReturn := ByteArray.empty }

def zeroSetupState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1121
    stack := [0, 0, UInt256.ofNat 0, UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)] }

def wordDispatchState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1122
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def wordCheckedState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1138
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
      UInt256.ofNat 1186, UInt256.ofNat modOff, UInt256.ofNat expOff,
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
  { wordEntryState input with pc := UInt256.ofNat 2042 }

/-- The unchanged dispatcher prefix followed by its retargeted final jump. -/
abbrev WordRouteEnter (input : ByteArray) : Type :=
  Challenge.EvmProof.GasSteps (Main.headerState input)
    (wordRouteEntryState input)

/-- A route miss must restore precisely the already-proved legacy entry. -/
abbrev WordRouteMiss (input : ByteArray) : Type :=
  Challenge.EvmProof.GasSteps (wordRouteEntryState input)
    (wordEntryState input)


end Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
