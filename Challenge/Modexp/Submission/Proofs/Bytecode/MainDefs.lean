import Challenge.Modexp.ProofSupport
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# MODEXP bytecode entry and header validation

This is the first execution certificate for the frozen artifact.  It follows
the compiler's function-declaration trampolines, reads the three EIP-198
header words, proves the EIP-7823 checks take their successful edge, and
stops at the operand dispatcher.  The same `GasSteps` witness is used by the
functional proof and by the exact gas schedule.
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

/-- First half of the compiler trampoline chain. -/
def trampoline1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 0 2 1202, opAt 1 .JUMP]

/-- Second half of the compiler trampoline chain. -/
def trampoline2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 903 .JUMPDEST]

/-- Three EIP-198 header loads. -/
def headerLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 904 0 0, opAt 905 .CALLDATALOAD,
   pushAt 906 1 32, opAt 907 .CALLDATALOAD,
   pushAt 908 1 64, opAt 909 .CALLDATALOAD]

/-- Successful EIP-7823 bound check. -/
def headerCheckPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 910 2 1024, opAt 911 (.Dup ⟨1, by decide⟩), opAt 912 .GT,
   pushAt 913 2 1024, opAt 914 (.Dup ⟨3, by decide⟩), opAt 915 .GT,
   pushAt 916 2 1024, opAt 917 (.Dup ⟨5, by decide⟩), opAt 918 .GT,
   opAt 919 .OR, opAt 920 .OR, opAt 921 .ISZERO,
   pushAt 922 2 1234, opAt 923 .JUMPI]

def headerModulusCheckPath :=
  [pushAt 910 2 1024, opAt 911 (.Dup ⟨1, by decide⟩), opAt 912 .GT]

def headerExponentCheckPath :=
  [pushAt 913 2 1024, opAt 914 (.Dup ⟨3, by decide⟩), opAt 915 .GT]

def headerBaseCheckPath :=
  [pushAt 916 2 1024, opAt 917 (.Dup ⟨5, by decide⟩), opAt 918 .GT]

def headerCheckFinishPath :=
  [opAt 919 .OR, opAt 920 .OR, opAt 921 .ISZERO,
   pushAt 922 2 1234, opAt 923 .JUMPI]

/-- Reachable instructions from byte zero through the successful header
check, retained as a single audit-friendly path. -/
def headerPath := trampoline1Path ++ trampoline2Path ++
  headerLoadPath ++ headerCheckPath

def tramp0Path := [pushAt 0 2 1202, opAt 1 .JUMP]
def tramp1Path := [opAt 12 .JUMPDEST, pushAt 13 2 53, opAt 14 .JUMP]
def tramp2Path := [opAt 43 .JUMPDEST, pushAt 44 2 99, opAt 45 .JUMP]
def tramp3Path := [opAt 80 .JUMPDEST, pushAt 81 2 305, opAt 82 .JUMP]
def tramp4Path := [opAt 262 .JUMPDEST, pushAt 263 2 434, opAt 264 .JUMP]
def tramp5Path := [opAt 350 .JUMPDEST, pushAt 351 2 512, opAt 352 .JUMP]
def tramp6Path := [opAt 412 .JUMPDEST, pushAt 413 2 699, opAt 414 .JUMP]
def tramp7Path := [opAt 560 .JUMPDEST, pushAt 561 2 1202, opAt 562 .JUMP,
  opAt 903 .JUMPDEST]
def tramp7JumpPath := [opAt 560 .JUMPDEST, pushAt 561 2 1202, opAt 562 .JUMP]
def tramp7DestPath := [opAt 903 .JUMPDEST]

def trampolineState (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

/-- Gas-erased state at the midpoint of the trampoline chain. -/
def trampolineMidState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat 305 }

/-- Gas-erased state at the public entry point. -/
def headerEntryState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat 1203 }

/-- Gas-erased state after loading the three header words. -/
def headerLoadedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1211
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerModulusCheckedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1216
    stack := [0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerExponentCheckedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1221
    stack := [0, 0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerBaseCheckedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1226
    stack := [0, 0, 0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

/-- Gas-erased state immediately after the successful size-check jump. -/
def headerState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1234
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
    Artifact.submissionArtifact.instructionPC i = [0, 3][i]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs12 (i : Nat) (hi : 12 ≤ i) (hii : i ≤ 14) :
    Artifact.submissionArtifact.instructionPC i = [14, 15, 18][i - 12]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs43 (i : Nat) (hi : 43 ≤ i) (hii : i ≤ 45) :
    Artifact.submissionArtifact.instructionPC i = [53, 54, 57][i - 43]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs80 (i : Nat) (hi : 80 ≤ i) (hii : i ≤ 82) :
    Artifact.submissionArtifact.instructionPC i = [99, 100, 103][i - 80]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs262 (i : Nat) (hi : 262 ≤ i) (hii : i ≤ 264) :
    Artifact.submissionArtifact.instructionPC i = [305, 306, 309][i - 262]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs350 (i : Nat) (hi : 350 ≤ i) (hii : i ≤ 352) :
    Artifact.submissionArtifact.instructionPC i = [434, 435, 438][i - 350]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs412 (i : Nat) (hi : 412 ≤ i) (hii : i ≤ 414) :
    Artifact.submissionArtifact.instructionPC i = [512, 513, 516][i - 412]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs560 (i : Nat) (hi : 560 ≤ i) (hii : i ≤ 562) :
    Artifact.submissionArtifact.instructionPC i = [699, 700, 703][i - 560]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs903 (i : Nat) (hi : 903 ≤ i) (hii : i ≤ 923) :
    Artifact.submissionArtifact.instructionPC i =
      [1202,1203,1204,1205,1207,1208,1210,1211,1214,1215,1216,
       1219,1220,1221,1224,1225,1226,1227,1228,1229,1232][i - 903]! := by
  interval_cases i <;> decide

@[simp] theorem jump14 :
    Decode.isValidJumpDest submissionBytecode 14 = true :=
  Artifact.isValidJumpDest_index 12 (by rfl)

@[simp] theorem jump53 :
    Decode.isValidJumpDest submissionBytecode 53 = true :=
  Artifact.isValidJumpDest_index 43 (by rfl)

@[simp] theorem jump99 :
    Decode.isValidJumpDest submissionBytecode 99 = true :=
  Artifact.isValidJumpDest_index 80 (by rfl)

@[simp] theorem jump305 :
    Decode.isValidJumpDest submissionBytecode 305 = true :=
  Artifact.isValidJumpDest_index 262 (by rfl)

@[simp] theorem jump434 :
    Decode.isValidJumpDest submissionBytecode 434 = true :=
  Artifact.isValidJumpDest_index 350 (by rfl)

@[simp] theorem jump512 :
    Decode.isValidJumpDest submissionBytecode 512 = true :=
  Artifact.isValidJumpDest_index 412 (by rfl)

@[simp] theorem jump699 :
    Decode.isValidJumpDest submissionBytecode 699 = true :=
  Artifact.isValidJumpDest_index 560 (by rfl)

@[simp] theorem jump1196 :
    Decode.isValidJumpDest submissionBytecode 1202 = true :=
  Artifact.isValidJumpDest_index 903 (by rfl)

@[simp] theorem jump1228 :
    Decode.isValidJumpDest submissionBytecode 1234 = true :=
  Artifact.isValidJumpDest_index 925 (by rfl)


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
