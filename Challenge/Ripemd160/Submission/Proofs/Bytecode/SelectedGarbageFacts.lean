import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
open EvmSemantics EvmSemantics.EVM

theorem selectedGarbage_zero (s : State) (i k : Nat)
    (h1 : k % 8 ≠ 1) (h2 : k % 8 ≠ 2) : selectedGarbage s i k = 0 := by
  unfold selectedGarbage
  split_ifs
  · rfl
  · simp only [PairedScheduleData.extractedGarbage, PairedScheduleData.extractedWordG,
      PairedScheduleData.chunkG, PairedScheduleData.extractedWord,
      if_neg (not_or_intro h1 h2), Nat.sub_self]

theorem selectedGarbage_thirteen (s : State) (i : Nat) : selectedGarbage s i 13 = 0 :=
  selectedGarbage_zero s i 13 (by decide) (by decide)

theorem selectedGarbage_eleven (s : State) (i : Nat) : selectedGarbage s i 11 = 0 :=
  selectedGarbage_zero s i 11 (by decide) (by decide)

#print axioms selectedGarbage_zero
#print axioms selectedGarbage_thirteen
#print axioms selectedGarbage_eleven
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel
