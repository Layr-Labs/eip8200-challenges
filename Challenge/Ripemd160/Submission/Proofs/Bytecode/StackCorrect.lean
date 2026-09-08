import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEndpointProvider
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixH1Miss
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixH1Seed
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedSuffixBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputExitBridge

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- The actual packed endpoint provider supplies every block-kernel field.
No legacy instruction trace or extra correctness premise is used here. -/
noncomputable def kernel : StackRunBridge.BlockKernel :=
  PackedKernelChoice.kernelFromWitness PackedEndpointProvider.endpointProvider

/-- Preserve the entry-prefix interface consumed by all outer guard branches. -/
theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 0x16c)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  classical
  by_cases hrec : PrefixBranch.Recognised input
  · let seed := PrefixH1Seed.seed input
    have inv := PrefixH1Seed.seedInvariant input hrec
    let suffix := PackedSuffixBridge.suffixRun kernel input hfit 1 seed inv
      (PrefixH1Seed.start_lt input hrec)
    have prefixTrace := PrefixH1Seed.gasSteps_hit_to_loop input hfit entryPrefix hrec
    have hcode : suffix.final.executionEnv.code = submissionBytecode := by
      rw [suffix.executionEnv]
      exact inv.code
    have hfork : suffix.final.fork = .Osaka := by
      change suffix.final.executionEnv.fork = .Osaka
      rw [suffix.executionEnv]
      exact inv.fork
    have hrun : suffix.final.halt = .Running :=
      suffix.halt.trans inv.running
    have hnp : Precompile.isPrecompileWithConfig
        suffix.final.executionEnv.precompileConfig suffix.final.executionEnv.fork
        suffix.final.executionEnv.codeAddr = false := by
      rw [suffix.executionEnv]
      exact inv.noPrecompile
    exact PackedOutputExitBridge.correct_of_driver_exit input suffix.final
      (prefixTrace.trans suffix.gasSteps) hcode hfork hrun hnp
      (suffix.callStack.trans inv.callStack) suffix.hashWords
  · exact StackRunBridge.correct_of_block_kernel kernel input hfit
      (PrefixH1Miss.gasSteps_padding_miss input hfit entryPrefix hrec)

#print axioms kernel
#print axioms correct

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
