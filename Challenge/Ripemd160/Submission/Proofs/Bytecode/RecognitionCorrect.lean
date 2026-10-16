import Challenge.Ripemd160.Submission.Proofs.Bytecode.GenericFramedCorrect
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
  apply J2Correct.from_entry input hn hfit hentry
  intro rho hcap hg
  have hb := RecognitionAccumulator.allowed_bounds input.size hn
  exact GenericFramedCorrect.correct input hfit hb.1 rho hcap hg

theorem from_loaded1000 (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 1000)
    (hentry : GasSteps (initialState submissionBytecode input 0) (PatternedScan.stS input 8158 [])) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  apply J2Correct.from_loaded1000 input hsize hfit hentry
  intro rho hcap hg
  have hb : 0 < input.size ∧ input.size ≤ 1000 := by omega
  exact GenericFramedCorrect.correct input hfit hb.1 rho hcap hg


#print axioms from_entry
#print axioms from_loaded1000
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect
