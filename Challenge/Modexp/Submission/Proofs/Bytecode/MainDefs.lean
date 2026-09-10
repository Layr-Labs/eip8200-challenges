import Challenge.Modexp.ProofSupport
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# MODEXP bytecode entry and header parsing

This module certifies the initial jump to the total early-word dispatcher.
It also retains the legacy header blocks reached after a wrapper miss and
fast-path fallback. Those blocks read the three EIP-198 length words and skip
the redundant size checks on the challenge's unchanged valid-input domain.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

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

/-- The initial jump to the total early-word dispatcher. -/
def trampoline1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 0 2 5318,
   opAt 1 .JUMP]

/-- The legacy body jump destination, reached after fallback. -/
def trampoline2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 894 .JUMPDEST]

/-- Three EIP-198 header loads. -/
def headerLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 895 0 0,
   opAt 896 .CALLDATALOAD,
   pushAt 897 1 32,
   opAt 898 .CALLDATALOAD,
   pushAt 899 1 64,
   opAt 900 .CALLDATALOAD]

/-- Direct jump over the EIP-7823 checks, justified by `Correct`'s valid-input
precondition. The jump preserves the three loaded length words. -/
def headerCheckPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 901 2 1190,
   opAt 902 .JUMP]

/-- Legacy header instruction inventory, with the separately routed entry jump. -/
def headerPath := trampoline1Path ++ trampoline2Path ++
  headerLoadPath ++ headerCheckPath

def tramp0Path := [pushAt 0 2 5318,
   opAt 1 .JUMP]
def tramp1Path := [pushAt 12 1 49,
   opAt 13 .JUMP]
def tramp2Path := [opAt 42 .JUMPDEST,
   pushAt 43 1 92,
   opAt 44 .JUMP]
def tramp3Path := [opAt 79 .JUMPDEST,
   pushAt 80 2 293,
   opAt 81 .JUMP]
def tramp4Path := [opAt 261 .JUMPDEST,
   pushAt 262 2 418,
   opAt 263 .JUMP]
def tramp5Path := [opAt 349 .JUMPDEST,
   pushAt 350 2 495,
   opAt 351 .JUMP]
def tramp6Path := [opAt 411 .JUMPDEST,
   pushAt 412 2 670,
   opAt 413 .JUMP]
def tramp7Path := [opAt 555 .JUMPDEST,
   pushAt 556 2 1158,
   opAt 557 .JUMP,
   opAt 894 .JUMPDEST]
def tramp7JumpPath := [opAt 555 .JUMPDEST,
   pushAt 556 2 1158,
   opAt 557 .JUMP]
def tramp7DestPath := [opAt 894 .JUMPDEST]

def trampolineState (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

/-- Gas-erased state at the midpoint of the trampoline chain. -/
def trampolineMidState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat 293 }

/-- Gas-erased state at the public entry point. -/
def headerEntryState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat 1159 }

/-- Gas-erased state after loading the three header words. -/
def headerLoadedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1167
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerModulusCheckedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1172
    stack := [0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerExponentCheckedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1177
    stack := [0, 0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerBaseCheckedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1182
    stack := [0, 0, 0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

/-- Gas-erased state immediately after the successful size-check jump. -/
def headerState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1190
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

theorem headerWord (input : ByteArray) (offset : Nat) :
    MachineState.readWord input offset =
      UInt256.ofNat (Precompile.bytesToNatPadded input offset 32) := rfl

theorem size_lt_word {n : Nat} (h : n ≤ 1024) : n < 2 ^ 256 := by
  omega

theorem boundedSize_gt_1024_eq_zero {n : Nat} (h : n ≤ 1024) :
    UInt256.gt (UInt256.ofNat n) 1024 = 0 := by
  have h1024 : (1024 : UInt256).toNat = 1024 := by decide
  rw [UInt256.gt, Challenge.EvmProof.Word.word_toNat_ofNat, h1024]
  rw [if_neg]
  · rfl
  · have hmod := Nat.mod_le n (2 ^ 256)
    omega

@[simp] theorem headerPCs0 (i : Nat) (hi : i ≤ 1) :
    Artifact.submissionArtifact.instructionPC i = [0,3][i]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs12 (i : Nat)
    (hi : 12 ≤ i) (hii : i ≤ 13) :
    Artifact.submissionArtifact.instructionPC i =
      ([14,16] : List Nat)[i - 12]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs43 (i : Nat)
    (hi : 42 ≤ i) (hii : i ≤ 44) :
    Artifact.submissionArtifact.instructionPC i =
      ([49,50,52] : List Nat)[i - 42]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs80 (i : Nat)
    (hi : 79 ≤ i) (hii : i ≤ 81) :
    Artifact.submissionArtifact.instructionPC i =
      ([92,93,96] : List Nat)[i - 79]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs262 (i : Nat)
    (hi : 261 ≤ i) (hii : i ≤ 263) :
    Artifact.submissionArtifact.instructionPC i =
      ([293,294,297] : List Nat)[i - 261]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs350 (i : Nat)
    (hi : 349 ≤ i) (hii : i ≤ 351) :
    Artifact.submissionArtifact.instructionPC i =
      ([418,419,422] : List Nat)[i - 349]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs412 (i : Nat)
    (hi : 411 ≤ i) (hii : i ≤ 413) :
    Artifact.submissionArtifact.instructionPC i =
      ([495,496,499] : List Nat)[i - 411]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs560 (i : Nat)
    (hi : 555 ≤ i) (hii : i ≤ 557) :
    Artifact.submissionArtifact.instructionPC i =
      ([670,671,674] : List Nat)[i - 555]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs899 (i : Nat)
    (hi : 894 ≤ i) (hii : i ≤ 914) :
    Artifact.submissionArtifact.instructionPC i =
      ([1158,1159,1160,1161,1163,1164,1166,1167,1170,1171,1172,1175,1176,1177,1180,1181,1182,1183,1184,1185,1188] : List Nat)[i - 894]! := by
  interval_cases i <;> decide

@[simp] theorem jump53 :
    Decode.isValidJumpDest submissionBytecode 49 = true :=
  Artifact.isValidJumpDest_index 42 (by rfl)

@[simp] theorem jump99 :
    Decode.isValidJumpDest submissionBytecode 92 = true :=
  Artifact.isValidJumpDest_index 79 (by rfl)

@[simp] theorem jump305 :
    Decode.isValidJumpDest submissionBytecode 293 = true :=
  Artifact.isValidJumpDest_index 261 (by rfl)

@[simp] theorem jump434 :
    Decode.isValidJumpDest submissionBytecode 418 = true :=
  Artifact.isValidJumpDest_index 349 (by rfl)

@[simp] theorem jump512 :
    Decode.isValidJumpDest submissionBytecode 495 = true :=
  Artifact.isValidJumpDest_index 411 (by rfl)

@[simp] theorem jump699 :
    Decode.isValidJumpDest submissionBytecode 670 = true :=
  Artifact.isValidJumpDest_index 555 (by rfl)

@[simp] theorem jump1196 :
    Decode.isValidJumpDest submissionBytecode 1158 = true :=
  Artifact.isValidJumpDest_index 894 (by rfl)

@[simp] theorem jump1228 :
    Decode.isValidJumpDest submissionBytecode 1190 = true :=
  Artifact.isValidJumpDest_index 916 (by rfl)


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
