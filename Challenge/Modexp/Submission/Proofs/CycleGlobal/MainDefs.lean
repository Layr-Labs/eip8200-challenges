import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.ProofSupport
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Word
noncomputable section
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

namespace CycleSubmission.Global.Main
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

/-- First half of the compiler trampoline chain. -/
def trampoline1Path :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

/-- Second half of the compiler trampoline chain. -/
def trampoline2Path :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 369 .JUMPDEST]

/-- Three EIP-198 header loads. -/
def headerLoadPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 370 0 0,
   opAt 371 .CALLDATALOAD,
   pushAt 372 1 32,
   opAt 373 .CALLDATALOAD,
   pushAt 374 1 64,
   opAt 375 .CALLDATALOAD]

/-- Direct hop over the EIP-7823 checks, justified by `Correct`'s valid-input
precondition. The last header load uses `PUSH3 64`, which frees two bytes for two `JUMPDEST`s,
so the block falls through to 1198 with an identical stack for 2 gas (was `PUSH2 1198 ; POP`,
5 gas). The `JUMPDEST` at 1198 stays in the code. The hop preserves the three loaded length words. -/
def headerCheckPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

/-- Reachable instructions from byte zero through optimized header parsing,
retained as a single audit-friendly path. -/
def headerPath := trampoline1Path ++ trampoline2Path ++
  headerLoadPath ++ headerCheckPath

def tramp0Path : List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) := []
def tramp7DestPath := [opAt 369 .JUMPDEST]

def trampolineState (input : ByteArray) (pc : Nat) : State :=
  { initialState CycleSubmission.Artifact.bytecode input 0 with pc := UInt256.ofNat pc }

/-- Gas-erased state at the public entry point. -/
def headerEntryState (input : ByteArray) : State :=
  { initialState CycleSubmission.Artifact.bytecode input 0 with pc := UInt256.ofNat 534 }

/-- Gas-erased state after loading the three header words. -/
def headerLoadedState (input : ByteArray) : State :=
  { initialState CycleSubmission.Artifact.bytecode input 0 with
    pc := UInt256.ofNat 542
    stack := [UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerModulusCheckedState (input : ByteArray) : State :=
  { initialState CycleSubmission.Artifact.bytecode input 0 with
    pc := UInt256.ofNat 542
    stack := [0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerExponentCheckedState (input : ByteArray) : State :=
  { initialState CycleSubmission.Artifact.bytecode input 0 with
    pc := UInt256.ofNat 542
    stack := [0, 0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerBaseCheckedState (input : ByteArray) : State :=
  { initialState CycleSubmission.Artifact.bytecode input 0 with
    pc := UInt256.ofNat 542
    stack := [0, 0, 0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

/-- Gas-erased state immediately after the successful size-check jump. -/
def headerState (input : ByteArray) : State :=
  { initialState CycleSubmission.Artifact.bytecode input 0 with
    pc := UInt256.ofNat 542
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
    CycleSubmission.Artifact.artifact.instructionPC i = [0, 2][i]! := by
  interval_cases i <;> decide

@[simp] theorem headerPCs899 (i : Nat)
    (hi : 369 ≤ i) (hii : i ≤ 376) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([533,534,535,536,538,539,541,542] : List Nat)[i - 369]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem jump1196 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 533 = true :=
  CycleSubmission.Global.Binding.jumpDest 369 (by rfl)



end CycleSubmission.Global.Main
