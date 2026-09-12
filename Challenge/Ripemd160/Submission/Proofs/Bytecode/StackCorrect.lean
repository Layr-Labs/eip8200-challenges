import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerIteration
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerIteration StaggerPersistentLoopInduction

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (_hpositive : 0 < input.size)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 272)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  apply StaggerPersistentCorrect.correct_of_blocks input hfit (states input) (hashes input)
    (states_zero input) (hashes_zero input) ?_ ?_
    (hashArray_hashes input hfit _ (Nat.le_refl _))
    (states_callStack input _) entryPrefix
  · intro i _
    exact ⟨states_code input i, states_fork input i, states_halt input i,
      states_noPrecompile input i⟩
  · intro i hi
    exact PersistentStaggerBlock.gasSteps (states input i) input i (hashes input i)
      (limitWord (DriverTrace.blockCount input)) [] (by decide) hfit hi
      (states_context input hfit i (Nat.le_of_lt hi))
      (states_code input i) (states_fork input i) (states_halt input i)
      (states_noPrecompile input i)
#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
