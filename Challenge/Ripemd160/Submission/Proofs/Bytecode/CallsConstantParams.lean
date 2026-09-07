import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantGroup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskParams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SingleCachedMaskInlineParams

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantParams

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackCompression QuadSemantic
open CavityQuadGroup
open CallsConstantGroup

abbrev Params := CavityQuadGroup.Params

abbrev left (group : Fin 5) (k : Fin 4) : Params := CachedMaskParams.left group k
abbrev right (group : Fin 5) (k : Fin 4) : Params :=
  SingleCachedMaskInlineParams.rightParams group k

def left2 : Fin 4 → Params := left 2
def left4 : Fin 4 → Params := left 4
def right0 : Fin 4 → Params := right 0
def right1 : Fin 4 → Params := right 1
def right2 : Fin 4 → Params := right 2

def left2Code : List Instr := cachedFourCode left2 0 (left2 0).constant 0
def left4Code : List Instr := cachedFourCode left4 2 (left4 0).constant 0
def right0Code : List Instr := cachedFourCode right0 2 (right0 0).constant 5
def right1Code : List Instr := cachedFourCode right1 1 (right1 0).constant 5
def right2Code : List Instr := cachedFourCode right2 0 (right2 0).constant 5

theorem left_fits (s : State) (group : Fin 5) (hactive : 11 ≤ s.activeWords.toNat) :
    ∀ k, (left group k).Fits s := by
  exact CachedMaskParams.left_fits s group hactive

theorem right_fits (s : State) (group : Fin 5)
    (hactive : 11 ≤ s.activeWords.toNat) : ∀ k, (right group k).Fits s := by
  intro k i
  have h := QuadSemantic.quadRightAddress_end_le s
    ⟨4 * group.val + k.val, by omega⟩ i hactive
  fin_cases group <;> fin_cases k <;> fin_cases i <;> exact h

theorem left_apply (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (group : Fin 5) (k : Fin 4)
    (hwords : QuadSemantic.DenseWordsAt s word) :
    (left group k).apply s w =
      leftStep word (16 * group.val + 4 * k.val + 3)
        (leftStep word (16 * group.val + 4 * k.val + 2)
          (leftStep word (16 * group.val + 4 * k.val + 1)
            (leftStep word (16 * group.val + 4 * k.val) w))) := by
  exact CachedMaskParams.left_apply s word w group k hwords

theorem right_apply (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (group : Fin 5) (k : Fin 4)
    (hwords : QuadSemantic.DenseWordsAt s word) :
    (right group k).apply s w =
      rightStep word (16 * group.val + 4 * k.val + 3)
        (rightStep word (16 * group.val + 4 * k.val + 2)
          (rightStep word (16 * group.val + 4 * k.val + 1)
            (rightStep word (16 * group.val + 4 * k.val) w))) := by
  have h := QuadSemantic.quadWorking_right s word w
    ⟨4 * group.val + k.val, by omega⟩ hwords
  fin_cases group <;> fin_cases k <;> exact h

theorem left_result_after (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (group : Fin 5)
    (hwords : QuadSemantic.DenseWordsAt s word) :
    cachedFourResult (left group) s (leftRounds word (16 * group.val) w) =
      leftRounds word (16 * group.val + 16) w := by
  rw [cachedFourResult, left_apply s word _ group 0 hwords,
    left_apply s word _ group 1 hwords,
    left_apply s word _ group 2 hwords,
    left_apply s word _ group 3 hwords]
  fin_cases group <;> rfl

theorem right_result_after (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (group : Fin 5)
    (hwords : QuadSemantic.DenseWordsAt s word) :
    cachedFourResult (right group) s (rightRounds word (16 * group.val) w) =
      rightRounds word (16 * group.val + 16) w := by
  rw [cachedFourResult, right_apply s word _ group 0 hwords,
    right_apply s word _ group 1 hwords,
    right_apply s word _ group 2 hwords,
    right_apply s word _ group 3 hwords]
  fin_cases group <;> rfl

theorem left2_function (k : Fin 4) : (left2 k).function.val = 2 := by rfl
theorem left4_function (k : Fin 4) : (left4 k).function.val = 4 := by rfl
theorem right0_function (k : Fin 4) : (right0 k).function.val = 4 := by rfl
theorem right1_function (k : Fin 4) : (right1 k).function.val = 3 := by rfl
theorem right2_function (k : Fin 4) : (right2 k).function.val = 2 := by rfl

theorem left2_constant (k : Fin 4) : (left2 k).constant = (left2 0).constant := by rfl
theorem left4_constant (k : Fin 4) : (left4 k).constant = (left4 0).constant := by rfl
theorem right0_constant (k : Fin 4) : (right0 k).constant = (right0 0).constant := by rfl
theorem right1_constant (k : Fin 4) : (right1 k).constant = (right1 0).constant := by rfl
theorem right2_constant (k : Fin 4) : (right2 k).constant = (right2 0).constant := by rfl

theorem left2_fits (s : State) (hactive : 11 ≤ s.activeWords.toNat) :
    ∀ k, (left2 k).Fits s := by
  exact left_fits s 2 hactive

theorem left4_fits (s : State) (hactive : 11 ≤ s.activeWords.toNat) :
    ∀ k, (left4 k).Fits s := by
  exact left_fits s 4 hactive

theorem right0_fits (s : State) (hactive : 11 ≤ s.activeWords.toNat) :
    ∀ k, (right0 k).Fits s := by
  exact right_fits s 0 hactive

theorem right1_fits (s : State) (hactive : 11 ≤ s.activeWords.toNat) :
    ∀ k, (right1 k).Fits s := by
  exact right_fits s 1 hactive

theorem right2_fits (s : State) (hactive : 11 ≤ s.activeWords.toNat) :
    ∀ k, (right2 k).Fits s := by
  exact right_fits s 2 hactive

theorem left2_result_after (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (hwords : QuadSemantic.DenseWordsAt s word) :
    cachedFourResult left2 s (leftRounds word 32 w) = leftRounds word 48 w := by
  simpa [left2] using left_result_after s word w 2 hwords

theorem left4_result_after (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (hwords : QuadSemantic.DenseWordsAt s word) :
    cachedFourResult left4 s (leftRounds word 64 w) = leftRounds word 80 w := by
  simpa [left4] using left_result_after s word w 4 hwords

theorem right0_result_after (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (hwords : QuadSemantic.DenseWordsAt s word) :
    cachedFourResult right0 s (rightRounds word 0 w) = rightRounds word 16 w := by
  simpa [right0] using right_result_after s word w 0 hwords

theorem right1_result_after (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (hwords : QuadSemantic.DenseWordsAt s word) :
    cachedFourResult right1 s (rightRounds word 16 w) = rightRounds word 32 w := by
  simpa [right1] using right_result_after s word w 1 hwords

theorem right2_result_after (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (hwords : QuadSemantic.DenseWordsAt s word) :
    cachedFourResult right2 s (rightRounds word 32 w) = rightRounds word 48 w := by
  simpa [right2] using right_result_after s word w 2 hwords

#print axioms left2_fits
#print axioms left2_result_after
#print axioms left4_result_after
#print axioms right0_result_after
#print axioms right1_result_after
#print axioms right2_result_after

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantParams
