import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144BlockBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentPaddedBlockBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentInputLoop
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStart
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentRun
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Table144Prepare

def states (input : ByteArray) : Nat → State
  | 0 => PersistentPaddingTrace.padReturned input
  | n+1 => scheduledState (states input n) n

def finalState (input : ByteArray) : State :=
  PersistentInputLoop.exitState (states input (DriverTrace.blockCount input)) input
    (StackRunBridge.hashStateAfter input (DriverTrace.blockCount input)) []

@[simp] theorem states_env (input : ByteArray) (n : Nat) :
    (states input n).executionEnv = (initialState submissionBytecode input 0).executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

@[simp] theorem states_halt (input : ByteArray) (n : Nat) : (states input n).halt = .Running := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

@[simp] theorem states_fork (input : ByteArray) (n : Nat) : (states input n).fork = .Osaka := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

@[simp] theorem states_callStack (input : ByteArray) (n : Nat) : (states input n).callStack = [] := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

@[simp] theorem states_calldata (input : ByteArray) (n : Nat) :
    (states input n).executionEnv.calldata = input := by rw [states_env]; rfl

@[simp] theorem states_code (input : ByteArray) (n : Nat) :
    (states input n).executionEnv.code = Artifact.submissionArtifact.code := by rw [states_env]; rfl

@[simp] theorem states_notPrecompile (input : ByteArray) (n : Nat) :
    Precompile.isPrecompileWithConfig (states input n).executionEnv.precompileConfig
      (states input n).executionEnv.fork (states input n).executionEnv.codeAddr = false := by
  rw [states_env]
  exact deployAddress_not_precompile

theorem states_ambient (input : ByteArray) (n : Nat) : PersistentLoopInduction.Ambient (states input n) :=
  ⟨states_code input n,states_fork input n,states_halt input n,states_notPrecompile input n⟩

theorem states_context (input : ByteArray) (hfit : CalldataFits input) (n j : Nat)
    (hj : j < DriverTrace.blockCount input) : Context (states input n) input j := by
  induction n with
  | zero =>
    constructor
    · rfl
    · exact PersistentPaddedBlockBridge.padReturned_blockIndexAt input hfit j hj
  | succ n ih => exact Table144BlockBridge.scheduled_context (states input n) input n j hfit hj ih

opaque gasSteps_block (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hi : i<DriverTrace.blockCount input) :
    GasSteps (Table144CallPrepare.callState (states input i) input i (StackRunBridge.hashStateAfter input i) [])
      (PersistentInputLoop.postState (states input (i+1)) input i (StackRunBridge.hashStateAfter input (i+1)) []) := by
  exact Table144BlockBridge.gasSteps_compress (states input i) input i
    (StackRunBridge.hashStateAfter input i) [] (by decide) hfit hi (states_context input hfit i i hi)
    (states_code input i) (states_fork input i) (states_halt input i) (states_notPrecompile input i)

opaque gasSteps_blocks (input : ByteArray) (hfit : CalldataFits input) :
    GasSteps (Table144CallPrepare.callState (states input 0) input 0 StackRunBridge.initialHashState [])
      (finalState input) :=
  PersistentInputLoop.run_input_blocks (states input) (StackRunBridge.hashStateAfter input) input [] hfit
    (by decide) (fun i _ => states_ambient input i) (gasSteps_block input hfit)

opaque gasSteps_start (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0<input.size) :
    GasSteps (PersistentPaddingTrace.padReturned input)
      (Table144CallPrepare.callState (states input 0) input 0 StackRunBridge.initialHashState []) := by
  have henv : (PersistentPaddingTrace.padReturned input).executionEnv.calldata = input := rfl
  have g := PersistentStart.gasSteps_positive (PersistentPaddingTrace.padReturned input)
    (UInt256.ofNat 0) (Padding.paddedWord input) [] (by decide) (PersistentPaddingTrace.padReturned_halt input)
    (by rw [henv]; exact lt_trans hfit (by decide)) (by rw [henv]; exact hpositive)
    (states_code input 0) (states_fork input 0) (states_notPrecompile input 0)
  exact g

noncomputable def gasSteps_run (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0<input.size)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 276)) :
    GasSteps (initialState submissionBytecode input 0) (finalState input) :=
  (PersistentPaddingTrace.gasSteps_pad input hfit entryPrefix).trans
    ((gasSteps_start input hfit hpositive).trans (gasSteps_blocks input hfit))

@[simp] theorem final_env (input : ByteArray) :
    (finalState input).executionEnv = (initialState submissionBytecode input 0).executionEnv :=
  states_env input _
@[simp] theorem final_halt (input : ByteArray) : (finalState input).halt = .Running := states_halt input _
@[simp] theorem final_fork (input : ByteArray) : (finalState input).fork = .Osaka := states_fork input _
@[simp] theorem final_callStack (input : ByteArray) : (finalState input).callStack = [] := states_callStack input _
@[simp] theorem final_code (input : ByteArray) :
    (finalState input).executionEnv.code = Artifact.submissionArtifact.code := states_code input _
@[simp] theorem final_notPrecompile (input : ByteArray) :
    Precompile.isPrecompileWithConfig (finalState input).executionEnv.precompileConfig
      (finalState input).executionEnv.fork (finalState input).executionEnv.codeAddr = false := states_notPrecompile input _

#print axioms states_context
#print axioms gasSteps_block
#print axioms gasSteps_blocks
#print axioms gasSteps_start
#print axioms gasSteps_run
#print axioms final_callStack
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentRun
