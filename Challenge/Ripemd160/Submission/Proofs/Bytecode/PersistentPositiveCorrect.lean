import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentRun
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentSerializeMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GasCost
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentPositiveCorrect
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof

def result (input : ByteArray) : State :=
  PersistentSerialize.result (PersistentRun.states input (DriverTrace.blockCount input))
    (StackRunBridge.hashStateAfter input (DriverTrace.blockCount input))
    (Padding.paddedWord input) (Padding.paddedWord input) []

opaque gasSteps_output (input : ByteArray) :
    GasSteps (PersistentRun.finalState input) (result input) := by
  exact PersistentSerialize.gasSteps (PersistentRun.states input (DriverTrace.blockCount input))
    (Padding.paddedWord input) (Padding.paddedWord input)
    (StackRunBridge.hashStateAfter input (DriverTrace.blockCount input)) [] (by decide)
    (PersistentRun.states_halt input _) (PersistentRun.states_code input _)
    (PersistentRun.states_fork input _) (PersistentRun.states_notPrecompile input _)

noncomputable def fullTrace (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 276)) :
    GasSteps (initialState submissionBytecode input 0) (result input) :=
  (PersistentRun.gasSteps_run input hfit hpositive entryPrefix).trans (gasSteps_output input)

theorem result_callStack (input : ByteArray) : (result input).callStack = [] :=
  PersistentRun.states_callStack input _
theorem result_halt (input : ByteArray) : (result input).halt = .Returned := rfl
theorem result_bytes (input : ByteArray) : (result input).hReturn = spec input :=
  PersistentSerialize.returned_spec _ input _ _ []

theorem correct_positive (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 276)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := fullTrace input hfit hpositive entryPrefix
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, State.isDone, State.isHalted, State.isRunning,
      result_callStack, result_halt])
  rw [State.toResult_returned _ (by exact result_halt input)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (result input).hReturn) at heval
  rw [result_bytes input] at heval
  simpa only [GasCost.withGas_initialState_zero] using heval

#print axioms correct_positive
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentPositiveCorrect
