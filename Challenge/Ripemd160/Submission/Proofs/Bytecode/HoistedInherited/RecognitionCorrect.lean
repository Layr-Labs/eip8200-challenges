import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.GenericFramedCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.J2Correct
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.RecognitionCorrect
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
abbrev of_returned := HoistedInherited.J2Correct.of_returned

theorem from_entry (input : ByteArray) (hfit : CalldataFits input)
    (hn : RecognitionAccumulator.Allowed input.size) (hne : input.size ≠ 1000)
    (hentry : GasSteps (initialState submissionBytecode input 0) (PatternedScan.patternedEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  apply HoistedInherited.J2Correct.from_entry input hn hne hfit hentry
  intro rho hcap hg
  have hb := RecognitionAccumulator.allowed_bounds input.size hn
  exact HoistedInherited.GenericFramedCorrect.correct input hfit hb.1 rho hcap hg

#print axioms from_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.RecognitionCorrect
