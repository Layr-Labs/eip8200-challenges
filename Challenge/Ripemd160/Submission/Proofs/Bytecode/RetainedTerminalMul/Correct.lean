import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.ActualBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.FallbackBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-! Universal 1000-byte scanner adapter, with the retained calldata word.
The zero-result case returns the proved digest; a miss clears the speculative
word and joins the generic compressor after its calldata copy. -/
namespace RetainedActual115
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open RetainedIntegration105 RetainedResultEdge112

theorem copied_initial (input : ByteArray) :
    RetainedFallback114.copied (initialState submissionBytecode input 0) [] =
      PaddingTrace.padCopied input := by
  simp only [RetainedFallback114.copied, PaddingTrace.padCopied,
    PaddingTrace.padCopyDone, PaddingTrace.padLengthReady, PaddingTrace.padEntry,
    Main.initializedState, List.append_nil]
  rfl

theorem from_loaded1000 (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 1000)
    (hentry : GasSteps (initialState submissionBytecode input 0)
      {PatternedScan.stS input 8157 [] with stack := [MachineState.readWord input 0]}) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let s := initialState submissionBytecode input 0
  have e : Env s := ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩
  by_cases hz : retainedResult input = 0
  · have gs := gasSteps_return s [] e (by decide) rfl hz
    have ht : GasSteps (initialState submissionBytecode input 0)
        (returned (stored s ExactBindings.digest) []) := hentry.trans gs
    exact J2Correct.of_returned input _ ht rfl rfl
      (returned_spec s [] hsize hz)
  · have gm := RetainedFallback114.gasSteps_miss_copy s [] e.toSidecar
      (by decide) (by exact Nat.lt_trans hfit (by norm_num))
      (by change 0 < input.size; omega) rfl rfl hz
    have gj : GasSteps (initialState submissionBytecode input 0)
        (PaddingTrace.padCopied input) := by
      rw [copied_initial] at gm
      exact hentry.trans gm
    have gp := PaddingTail.gasSteps_push input [] (by decide)
    have gt : GasSteps (initialState submissionBytecode input 0)
        (StackTail.append (PaddingTrace.padFramed input) []) := by
      exact gj.trans gp
    exact GenericFramedCorrect.correct input hfit (by omega) [] (by decide) gt

#print axioms copied_initial
#print axioms from_loaded1000
end RetainedActual115
