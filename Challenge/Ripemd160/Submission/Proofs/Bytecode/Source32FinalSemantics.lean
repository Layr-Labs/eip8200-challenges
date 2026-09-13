import Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32Ready
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCorrect
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32FinalSemantics
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof

theorem hashAfter_of_ready (memory input : ByteArray) (h32 : input.size = 32)
    (hr : StaggerMessage.Ready memory (PersistentStaggerTable.blockWords input 0)) :
    CompressionCorrect.hashArray
      (PersistentStaggerFunctional.result memory StackRunBridge.initialHashState) =
      CompressionSeamBridge.hashAfter input (DriverTrace.blockCount input) := by
  have hh := PersistentStaggerFunctional.result_compressBlock memory
    (Padding.paddedMessage input) 0 StackRunBridge.initialHashState hr
  have hb : DriverTrace.blockCount input = 1 := by
    simp [DriverTrace.blockCount, Padding.paddedLength, h32]
  rw [hb, hh]
  simp only [CompressionSeamBridge.hashAfter, SpecBridge.absorbBlocks_succ,
    SpecBridge.absorbBlocks_zero, Nat.zero_mul, Nat.add_zero]
  rfl

theorem eval_of_return_trace (code input : ByteArray) (t : State)
    (trace : GasSteps (initialState code input 0) t)
    (hr : t.halt = .Returned) (hc : t.callStack = []) (hb : t.hReturn = spec input) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState code input gas) (.returned (spec input)) := by
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, State.isDone, State.isHalted, State.isRunning, hc, hr])
  rw [State.toResult_returned _ (by exact hr)] at heval
  change Eval (withGas (initialState code input 0) gas) (.returned t.hReturn) at heval
  rw [hb] at heval
  simpa only [GasCost.withGas_initialState_zero] using heval

#print axioms hashAfter_of_ready
#print axioms eval_of_return_trace
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Source32FinalSemantics
