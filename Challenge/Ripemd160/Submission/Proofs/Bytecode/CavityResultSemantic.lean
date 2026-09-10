import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSemantic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityResultSemantic

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open CavityQuadGroup CavityParams QuadSemantic StackCompression

def leftQuad (word : Nat → UInt32) (k : Fin 4) (w : Compression.EvmWorking) :
    Compression.EvmWorking :=
  leftStep word (4 * k.val + 3)
    (leftStep word (4 * k.val + 2)
      (leftStep word (4 * k.val + 1) (leftStep word (4 * k.val) w)))

def rightQuad (word : Nat → UInt32) (k : Fin 4) (w : Compression.EvmWorking) :
    Compression.EvmWorking :=
  rightStep word (64 + 4 * k.val + 3)
    (rightStep word (64 + 4 * k.val + 2)
      (rightStep word (64 + 4 * k.val + 1) (rightStep word (64 + 4 * k.val) w)))

theorem left_fits (s : State) (hactive : 11 ≤ s.activeWords.toNat) :
    ∀ k, (left k).Fits s := by
  intro k i
  have h := quadLeftAddress_end_le s ⟨k.val, by omega⟩ i hactive
  fin_cases k <;> fin_cases i <;> exact h

theorem right_fits (s : State) (hactive : 11 ≤ s.activeWords.toNat) :
    ∀ k, (right k).Fits s := by
  intro k i
  have h := quadRightAddress_end_le s ⟨16 + k.val, by omega⟩ i hactive
  fin_cases k <;> fin_cases i <;> exact h

theorem left_apply (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (k : Fin 4) (hwords : DenseWordsAt s word) :
    (left k).apply s w = leftQuad word k w := by
  have h := quadWorking_left s word w ⟨k.val, by omega⟩ hwords
  fin_cases k <;> exact h

theorem right_apply (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (k : Fin 4) (hwords : DenseWordsAt s word) :
    (right k).apply s w = rightQuad word k w := by
  have h := quadWorking_right s word w ⟨16 + k.val, by omega⟩ hwords
  fin_cases k <;> exact h

/-- The cavity computes all first sixteen left rounds for arbitrary message words. -/
theorem left_result (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (hwords : DenseWordsAt s word) :
    leftResult s w = leftRounds word 16 w := by
  rw [leftResult, left_apply s word _ _ hwords, left_apply s word _ _ hwords,
    left_apply s word _ _ hwords, left_apply s word _ _ hwords]
  rfl

theorem right_result (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (hwords : DenseWordsAt s word) :
    rightResult s w =
      rightQuad word 3 (rightQuad word 2 (rightQuad word 1 (rightQuad word 0 w))) := by
  rw [rightResult, right_apply s word _ _ hwords, right_apply s word _ _ hwords,
    right_apply s word _ _ hwords, right_apply s word _ _ hwords]

/-- Applied after round64, the right cavity completes all eighty right rounds. -/
theorem right_result_after64 (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (hwords : DenseWordsAt s word) :
    rightResult s (rightRounds word 64 w) = rightRounds word 80 w := by
  rw [right_result s word _ hwords]
  rfl

#print axioms left_fits
#print axioms right_fits
#print axioms left_result
#print axioms right_result_after64

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityResultSemantic
