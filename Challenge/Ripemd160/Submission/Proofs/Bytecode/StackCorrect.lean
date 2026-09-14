import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdTailCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32TailCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Correct
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 600000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 341)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases h32 : input.size = 32
  · exact Shared32Correct.correct input h32 entryPrefix
  · exact ColdCorrect.correct input hfit hpositive h32 entryPrefix
theorem correct_tail (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hsmall : input.size < 5218)
    (rho : List UInt256) (hcap : rho.length ≤ 20)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (StackTail.append (Execution.atPC input 341) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases h32 : input.size = 32
  · exact Shared32TailCorrect.correct input h32 rho hcap entryPrefix
  · exact ColdTailCorrect.correct input hfit hpositive h32 hsmall rho hcap entryPrefix
#print axioms correct_tail
#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
