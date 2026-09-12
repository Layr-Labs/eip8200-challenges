import Challenge.Modexp.ProofSupport
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# MODEXP bytecode entry and header parsing

This is the first execution certificate for the frozen artifact. It follows
the optimized entry jump, reads the three EIP-198 header words, skips the
redundant EIP-7823 checks on the challenge's already-valid domain, and stops at
the operand dispatcher. The same `GasSteps` witness is used by the functional
proof and by the exact gas schedule.
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
  [pushAt 0 2 5178, opAt 1 .JUMP]

/-- Second half of the compiler trampoline chain. -/
def trampoline2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 813 .JUMPDEST]

/-- Three EIP-198 header loads. -/
def headerLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 814 0 0, opAt 815 .CALLDATALOAD,
   pushAt 816 1 32, opAt 817 .CALLDATALOAD,
   pushAt 818 1 64, opAt 819 .CALLDATALOAD]

/-- Direct jump over the EIP-7823 checks, justified by `Correct`'s valid-input
precondition. The jump preserves the three loaded length words. -/
def headerCheckPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 820 2 1067, opAt 821 .JUMP]

/-- Reachable instructions from byte zero through optimized header parsing,
retained as a single audit-friendly path. -/
def headerPath := trampoline1Path ++ trampoline2Path ++
  headerLoadPath ++ headerCheckPath

def tramp0Path := [pushAt 0 2 5178, opAt 1 .JUMP]
def tramp7DestPath := [opAt 813 .JUMPDEST]

def trampolineState (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

/-- Gas-erased state at the public entry point. -/
def headerEntryState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat 1055 }

/-- Gas-erased state after loading the three header words. -/
def headerLoadedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1063
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerModulusCheckedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1067
    stack := [0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerExponentCheckedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1067
    stack := [0, 0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerBaseCheckedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1067
    stack := [0, 0, 0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

/-- Gas-erased state immediately after the successful size-check jump. -/
def headerState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1067
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

@[simp] theorem headerPCs899 (i : Nat)
    (hi : 813 ≤ i) (hii : i ≤ 821) :
    Artifact.submissionArtifact.instructionPC i =
      ([1054,1055,1056,1057,1059,1060,1062,1063,1066] : List Nat)[i - 813]! := by
  interval_cases i <;> decide

@[simp] theorem jump1196 :
    Decode.isValidJumpDest submissionBytecode 1054 = true :=
  Artifact.isValidJumpDest_index 813 (by rfl)

@[simp] theorem jump1228 :
    Decode.isValidJumpDest submissionBytecode 1067 = true :=
  Artifact.isValidJumpDest_index 822 (by rfl)


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
