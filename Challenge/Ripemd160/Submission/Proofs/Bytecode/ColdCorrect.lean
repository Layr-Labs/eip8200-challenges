import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryCorrect
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 600000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdCorrect
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

/-- Every non-32-byte hash input takes the ordinary block loop.  Whole-block inputs of 256
bytes or more enter it through the cold padding path (the fast entry admits only 64, 128 and
192 bytes), so the pad-only block never meets a length whose high length words are set. -/
theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 247)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) :=
  ColdOrdinaryCorrect.correct input hfit hpositive hn32 entryPrefix

#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdCorrect
