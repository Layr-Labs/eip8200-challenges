import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerIteration
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryCorrect
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerIteration StaggerPersistentLoopInduction

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32)
    (hordinary : ∀ i, i<DriverTrace.blockCount input → input.size=DriverTrace.blockOffset i → input.size<5245)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 247)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  apply StaggerPersistentCorrect.correct_of_blocks input hfit hpositive hn32 (states input) (hashes input)
    (states_zero input) (hashes_zero input) ?_ ?_
    (hashArray_hashes input hfit hpositive _ (Nat.le_refl _))
    (states_callStack input _) entryPrefix
  · intro i _
    exact ⟨states_code input i, states_fork input i, states_halt input i,
      states_noPrecompile input i, states_calldata input i⟩
  · intro i hi
    exact ColdOrdinaryBlock.gasSteps (states input i) input i (hashes input i)
      (LoopCompletionControl.limit input) [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]
      (by decide) [] rfl hfit hi
      (states_context input hfit hpositive i (Nat.le_of_lt hi)) (hordinary i hi)
      (states_code input i) (states_fork input i) (states_halt input i)
      (states_noPrecompile input i)
#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryCorrect
