import Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.CompressionRunTrace
import Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.CompressionSeamBridge
import Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.OutputResultBridge

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

/-!
# Universal fallback trace

The copied functional closure starts at the post-`JUMPDEST` state.  The
caller supplies the finite prefix from the challenge initial state.
-/

namespace Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.FallbackCorrect

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

noncomputable def fallbackSeam (input : ByteArray) (hfit : CalldataFits input) :
    DirectCorrect.CompressionSeam input :=
  CompressionSeamBridge.toCompressionSeam
    (CompressionRunTrace.compressionRun input hfit)

noncomputable def fallbackFinal (input : ByteArray) (hfit : CalldataFits input) : State :=
  DirectCorrect.outputResult
    ((fallbackSeam input hfit).states (DriverTrace.blockCount input)) input

noncomputable def fallbackTrace (input : ByteArray) (hfit : CalldataFits input) :
    GasSteps (Execution.mainStart input) (fallbackFinal input hfit) := by
  simpa [fallbackFinal] using
    DirectCorrect.fullTrace input hfit (fallbackSeam input hfit)

theorem fallbackFinal_isDone (input : ByteArray) (hfit : CalldataFits input) :
    (fallbackFinal input hfit).isDone = true := by
  simpa [fallbackFinal] using
    OutputResultBridge.final_isDone input (fallbackSeam input hfit)

theorem fallbackFinal_result (input : ByteArray) (hfit : CalldataFits input) :
    (fallbackFinal input hfit).toResult = .returned (spec input) := by
  simpa [fallbackFinal] using
    OutputResultBridge.final_result input (fallbackSeam input hfit)

theorem fallbackEventuallyEvaluates :
    EventuallyEvaluates
      (Input := { input : ByteArray // CalldataFits input })
      (fun input gas => withGas (Execution.mainStart input.1) gas)
      (fun input => .returned (spec input.1)) := by
  let Input := { input : ByteArray // CalldataFits input }
  have h := GasSteps.toEventuallyEvaluates
    (initial := fun input : Input => Execution.mainStart input.1)
    (final := fun input : Input => fallbackFinal input.1 input.2)
    (expected := fun input : Input => .returned (spec input.1))
    (fun input => fallbackTrace input.1 input.2)
    (fun input => fallbackFinal_isDone input.1 input.2)
    (fun input => fallbackFinal_result input.1 input.2)
  simpa [Input] using h

theorem correct_from_prefix (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState referenceBytecode input 0)
      (Execution.mainStart input)) :
    ∃ g0, ∀ g, g0 ≤ g →
      Eval (initialState referenceBytecode input g) (.returned (spec input)) := by
  let trace := entryPrefix.trans (fallbackTrace input hfit)
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := Challenge.EvmProof.eval_of_steps (trace.trace gas hgas) (by
    change (fallbackFinal input hfit).isDone = true
    exact fallbackFinal_isDone input hfit)
  change Eval (withGas (initialState referenceBytecode input 0) gas)
    (withGas (fallbackFinal input hfit) (gas - trace.cost)).toResult at heval
  have hfinal :
      (withGas (fallbackFinal input hfit) (gas - trace.cost)).toResult =
        .returned (spec input) := by
    change (fallbackFinal input hfit).toResult = .returned (spec input)
    exact fallbackFinal_result input hfit
  have hinitial :
      withGas (initialState referenceBytecode input 0) gas =
        initialState referenceBytecode input gas := by
    rfl
  rw [hfinal, hinitial] at heval
  exact heval

end Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.FallbackCorrect
