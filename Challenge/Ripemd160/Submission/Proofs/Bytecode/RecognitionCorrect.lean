import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Correct
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
abbrev of_returned := J2Correct.of_returned

theorem from_entry (input : ByteArray) (hfit : CalldataFits input)
    (hn : RecognitionAccumulator.Allowed input.size)
    (hentry : GasSteps (initialState submissionBytecode input 0) (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  apply J2Correct.from_entry input hn hentry
  intro rho hcap hg
  have hb := RecognitionAccumulator.allowed_bounds input.size hn
  exact StackCorrect.correct_tail input hfit hb.1 (by omega) rho hcap hg

#print axioms from_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect
