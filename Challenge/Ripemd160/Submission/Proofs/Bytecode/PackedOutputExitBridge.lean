import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastOutputResultBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge

set_option warningAsError true
set_option autoImplicit false

/-!
# Packed output bridge from an externally certified driver exit

This module deliberately starts after the block driver.  Its caller supplies
the concrete `GasSteps` trace to `DriverTrace.afterExit`, so this bridge works
for both the ordinary padding path and a prefix-recognition path that seeds the
driver after an already-compressed first block.  It does not invoke or assume
the old `PaddingTrace.gasSteps_pad` path.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputExitBridge

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- The five certified final chaining words serialize to the challenge result.
This is independent of how execution reached the driver's exit. -/
theorem outputBytes_eq_spec (input : ByteArray) (final : State)
    (hwords : CompressionSeamBridge.HashWordsAt input
      (DriverTrace.blockCount input) final) :
    FastOutputResultBridge.outputBytes final = spec input := by
  let H := SpecBridge.absorbBlocks Crypto.Ripemd160.H0
    (Padding.paddedMessage input) 0 (DriverTrace.blockCount input)
  rw [FastOutputResultBridge.outputBytes_eq_emitDigest final H hwords]
  rw [FastOutputResultBridge.spec_eq, ← HashSpecBridge.paddedHash_eq_hash input]
  rfl

/-- Append the exact final-output bytecode to any externally certified driver
exit.  The supplied state facts are precisely those consumed by the located
output site; no padding or compression trace is reconstructed here. -/
def gasSteps_outputFromDriverExit (input : ByteArray) (final : State)
    (prefixTrace : GasSteps (initialState submissionBytecode input 0)
      (DriverTrace.afterExit final input))
    (hcode : final.executionEnv.code = submissionBytecode)
    (hfork : final.fork = .Osaka) (hrun : final.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig final.executionEnv.precompileConfig
      final.executionEnv.fork final.executionEnv.codeAddr = false) :
    GasSteps (initialState submissionBytecode input 0)
      (FastOutputResultBridge.outputState final input) := by
  have output := FastOutputSite.gasSteps_fastOutput final
    (FastOutputResultBridge.driverRest input)
    (by simp [FastOutputResultBridge.driverRest]) hcode hfork hrun hnp
  exact prefixTrace.trans (by
    simpa only [DriverTrace.afterExit, FastOutputResultBridge.outputState,
      FastOutputResultBridge.driverRest] using output)

/-- End-to-end correctness from an externally supplied driver-exit trace and
the final five-word hash invariant.  This is the output half shared by normal
misses and recognised-prefix executions. -/
theorem correct_of_driver_exit (input : ByteArray) (final : State)
    (prefixTrace : GasSteps (initialState submissionBytecode input 0)
      (DriverTrace.afterExit final input))
    (hcode : final.executionEnv.code = submissionBytecode)
    (hfork : final.fork = .Osaka) (hrun : final.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig final.executionEnv.precompileConfig
      final.executionEnv.fork final.executionEnv.codeAddr = false)
    (hcalls : final.callStack = [])
    (hwords : CompressionSeamBridge.HashWordsAt input
      (DriverTrace.blockCount input) final) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := gasSteps_outputFromDriverExit input final prefixTrace
    hcode hfork hrun hnp
  have hcall :
      (FastOutputResultBridge.outputState final input).callStack = [] := hcalls
  have hreturned :
      (FastOutputResultBridge.outputState final input).halt = .Returned := by
    rfl
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := Challenge.EvmProof.eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, State.isDone, State.isHalted, State.isRunning,
      hcall, hreturned])
  rw [State.toResult_returned _ (by rfl)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (FastOutputResultBridge.outputBytes final)) at heval
  rw [outputBytes_eq_spec input final hwords] at heval
  simpa [GasCost.withGas_initialState_zero] using heval

#print axioms outputBytes_eq_spec
#print axioms gasSteps_outputFromDriverExit
#print axioms correct_of_driver_exit

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputExitBridge
