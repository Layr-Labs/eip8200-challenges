import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentPaddingTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStart
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentEmpty

set_option warningAsError true
set_option maxRecDepth 100000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentEmptyCorrect
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

theorem correct_empty (input : ByteArray) (hfit : CalldataFits input) (hempty : input.size = 0)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 276)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let s := PersistentPaddingTrace.padReturned input
  let off := UInt256.ofNat 0
  let limit := PersistentPadding.paddedWord input
  let frame := PersistentFrame.frame StackRunBridge.initialHashState off limit []
  have hp := PersistentPaddingTrace.gasSteps_pad input hfit entryPrefix
  have hs := PersistentStart.gasSteps_empty s off limit [] (by decide)
    (PersistentPaddingTrace.padReturned_halt input) hempty
    (PersistentPaddingTrace.padReturned_code input)
    (PersistentPaddingTrace.padReturned_fork input)
    (PersistentPaddingTrace.padReturned_noPrecompile input)
  have he := PersistentEmpty.gasSteps_empty s StackRunBridge.initialHashState off limit []
    (by decide) (PersistentPaddingTrace.padReturned_halt input)
    (PersistentPaddingTrace.padReturned_code input)
    (PersistentPaddingTrace.padReturned_fork input)
    (PersistentPaddingTrace.padReturned_noPrecompile input)
  let trace := hp.trans (hs.trans he)
  have hinput : input = ByteArray.empty := by
    apply ByteArray.ext
    apply Array.ext
    · simpa using hempty
    · intro i hi
      simp [hempty] at hi
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by rfl)
  rw [State.toResult_returned _ (by rfl)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (PersistentEmpty.result s frame).hReturn) at heval
  rw [PersistentEmpty.returned_bytes, ← hinput] at heval
  exact heval

#print axioms correct_empty
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentEmptyCorrect
