import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTable
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerFunctional
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddedBlockBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerIteration
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable

def states (input : ByteArray) : Nat → State
  | 0 => PaddingTrace.padReturned input
  | n + 1 => scheduledState (states input n) n

def hashes (input : ByteArray) : Nat → Compression.HashState
  | 0 => StackRunBridge.initialHashState
  | n + 1 => PersistentStaggerFunctional.result (states input (n + 1)).memory (hashes input n)

@[simp] theorem states_zero (input : ByteArray) : states input 0 = PaddingTrace.padReturned input := rfl
@[simp] theorem states_succ (input : ByteArray) (n : Nat) :
    states input (n + 1) = scheduledState (states input n) n := rfl
@[simp] theorem hashes_zero (input : ByteArray) : hashes input 0 = StackRunBridge.initialHashState := rfl
@[simp] theorem hashes_succ (input : ByteArray) (n : Nat) :
    hashes input (n + 1) =
      PersistentStaggerFunctional.result (scheduledState (states input n) n).memory (hashes input n) := rfl

theorem states_executionEnv (input : ByteArray) (n : Nat) :
    (states input n).executionEnv = (PaddingTrace.padReturned input).executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem states_halt (input : ByteArray) (n : Nat) : (states input n).halt = .Running := by
  induction n with
  | zero => exact PaddingTrace.padReturned_halt input
  | succ n ih => exact ih

theorem states_callStack (input : ByteArray) (n : Nat) : (states input n).callStack = [] := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem states_calldata (input : ByteArray) (n : Nat) :
    (states input n).executionEnv.calldata = input := by
  rw [states_executionEnv]
  rfl

theorem states_code (input : ByteArray) (n : Nat) :
    (states input n).executionEnv.code = submissionBytecode := by
  rw [states_executionEnv]
  exact PaddingTrace.padReturned_code input

theorem states_fork (input : ByteArray) (n : Nat) : (states input n).fork = .Osaka := by
  change (states input n).executionEnv.fork = .Osaka
  rw [states_executionEnv]
  exact PaddingTrace.padReturned_fork input

theorem states_noPrecompile (input : ByteArray) (n : Nat) :
    Precompile.isPrecompileWithConfig (states input n).executionEnv.precompileConfig
      (states input n).executionEnv.fork (states input n).executionEnv.codeAddr = false := by
  rw [states_executionEnv]
  exact PaddingTrace.padReturned_noPrecompile input

theorem initial_context (input : ByteArray) (hfit : CalldataFits input) :
    Context (PaddingTrace.padReturned input) input := by
  refine ⟨rfl, Nat.le_refl _, ?_, ?_⟩
  · intro i hi
    exact PaddedBlockBridge.padReturned_blockIndexAt input hfit i hi
  · intro i hi
    exact PaddedBlockBridge.padReturned_blockIndexSeparated input hfit i hi

theorem states_context (input : ByteArray) (hfit : CalldataFits input)
    (n : Nat) (hn : n ≤ DriverTrace.blockCount input) : Context (states input n) input := by
  induction n with
  | zero => exact initial_context input hfit
  | succ n ih =>
    exact Context.scheduled (states input n) input n hfit (by omega) (ih (by omega))

theorem states_activeWords (input : ByteArray) (hfit : CalldataFits input)
    (n : Nat) (hn : n ≤ DriverTrace.blockCount input) :
    (states input n).activeWords = (PaddingTrace.padReturned input).activeWords := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (scheduled_active_eq (states input n) input n hfit (by omega)
      (states_context input hfit n (by omega))).trans (ih (by omega))

theorem states_active_ge34 (input : ByteArray) (hfit : CalldataFits input)
    (n : Nat) (hn : n ≤ DriverTrace.blockCount input) :
    34 ≤ (states input n).activeWords.toNat := by
  rw [states_activeWords input hfit n hn]
  have ha := PaddingTrace.padReturned_allocated input hfit
  have hb := DriverTrace.blockCount_pos input
  have hl := DriverTrace.paddedLength_eq_blockCount input
  unfold Padding.messageOffset at ha
  omega

theorem states_word_above (input : ByteArray) (n address : Nat) (ha : 1152 ≤ address) :
    MachineState.readWord (states input n).memory address =
      MachineState.readWord (PaddingTrace.padReturned input).memory address := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (scheduled_word_above (states input n) n address ha).trans ih

theorem states_ready (input : ByteArray) (hfit : CalldataFits input)
    (n : Nat) (hn : n < DriverTrace.blockCount input) :
    StaggerMessage.Ready (states input (n + 1)).memory (blockWords input n) :=
  ready (states input n) input n hfit hn (states_context input hfit n (by omega))

theorem hashArray_hashes (input : ByteArray) (hfit : CalldataFits input)
    (n : Nat) (hn : n ≤ DriverTrace.blockCount input) :
    CompressionCorrect.hashArray (hashes input n) = CompressionSeamBridge.hashAfter input n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hashes]
    rw [PersistentStaggerFunctional.result_compressBlock
      (states input (n + 1)).memory (Padding.paddedMessage input)
      (DriverTrace.blockOffset n) (hashes input n) (states_ready input hfit n (by omega))]
    rw [ih (by omega), StackRunBridge.hashAfter_succ]
    rfl

#print axioms initial_context
#print axioms states_context
#print axioms states_activeWords
#print axioms states_ready
#print axioms hashArray_hashes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerIteration
