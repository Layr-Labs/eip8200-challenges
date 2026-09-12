import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentPositiveCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentEmptyCorrect
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 276)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hempty : input.size = 0
  · exact PersistentEmptyCorrect.correct_empty input hfit hempty entryPrefix
  · exact PersistentPositiveCorrect.correct_positive input hfit (Nat.pos_of_ne_zero hempty) entryPrefix

#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
