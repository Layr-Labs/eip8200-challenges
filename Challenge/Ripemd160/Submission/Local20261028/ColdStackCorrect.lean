import Challenge.Ripemd160.Submission.Local20261028.ColdGenericFramedCorrect
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.StackCorrect
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

theorem correct_tail (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0 < input.size)
    (rho : List UInt256) (hs : rho.length ≤ 20)
    (prefixTrace : GasSteps (initialState submissionBytecode input 0)
      (StackTail.append (Execution.atPC input 246) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas → Eval (initialState submissionBytecode input gas) (.returned (Challenge.Ripemd160.spec input)) :=
  GenericFramedCorrect.correct input hfit hpositive rho hs
    (prefixTrace.trans (PaddingTail.gasSteps_prefix input hfit rho hs))

theorem correct (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0 < input.size)
    (prefixTrace : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 246)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas → Eval (initialState submissionBytecode input gas) (.returned (Challenge.Ripemd160.spec input)) :=
  correct_tail input hfit hpositive [] (by decide) prefixTrace
#print axioms correct_tail
#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.StackCorrect
