import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskQuadGroup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityResultSemantic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskParams

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open CavityQuadGroup CachedMaskQuadGroup QuadSemantic StackCompression

/-- Control parameters for any complete sixteen-round left group. -/
def left (group : Fin 5) (k : Fin 4) : Params where
  function := group
  address i := StackRoundData.leftAddress (16 * group.val + 4 * k.val + i.val)
  rotation i := StackRoundData.leftRotation (16 * group.val + 4 * k.val + i.val)
  constant := StackRoundData.leftConstant (16 * group.val)
  rotations_bounded i := StackRoundData.leftRotation_le_32
    ⟨16 * group.val + 4 * k.val + i.val, by omega⟩
  constant_zero h := by
    have heq : group = 0 := Fin.ext h
    subst group
    rfl

abbrev right := CavityParams.right

def leftCode (group : Fin 5) : List YulEvmCompiler.Instr := fourCode (left group) 0
def rightCode : List YulEvmCompiler.Instr := fourCode right 5

def leftQuad (word : Nat → UInt32) (group : Fin 5) (k : Fin 4)
    (w : Compression.EvmWorking) : Compression.EvmWorking :=
  leftStep word (16 * group.val + 4 * k.val + 3)
    (leftStep word (16 * group.val + 4 * k.val + 2)
      (leftStep word (16 * group.val + 4 * k.val + 1)
        (leftStep word (16 * group.val + 4 * k.val) w)))

theorem left_fits (s : State) (group : Fin 5) (hactive : 61 ≤ s.activeWords.toNat) :
    ∀ k, (left group k).Fits s := by
  intro k i
  have h := quadLeftAddress_end_le s ⟨4 * group.val + k.val, by omega⟩ i hactive
  fin_cases group <;> fin_cases k <;> fin_cases i <;> exact h

theorem left_apply (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (group : Fin 5) (k : Fin 4)
    (hwords : DenseWordsAt s word) :
    (left group k).apply s w = leftQuad word group k w := by
  have h := quadWorking_left s word w ⟨4 * group.val + k.val, by omega⟩ hwords
  fin_cases group <;> fin_cases k <;> exact h

theorem left_result_after (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (group : Fin 5) (hwords : DenseWordsAt s word) :
    fourResult (left group) s (leftRounds word (16 * group.val) w) =
      leftRounds word (16 * group.val + 16) w := by
  rw [fourResult, left_apply s word _ _ _ hwords, left_apply s word _ _ _ hwords,
    left_apply s word _ _ _ hwords, left_apply s word _ _ _ hwords]
  fin_cases group <;> rfl

theorem right_result_after64 (s : State) (word : Nat → UInt32)
    (w : Compression.EvmWorking) (hwords : DenseWordsAt s word) :
    fourResult right s (rightRounds word 64 w) = rightRounds word 80 w := by
  exact CavityResultSemantic.right_result_after64 s word w hwords

theorem run_leftCode (group : Fin 5) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rho : List UInt256)
    (hfit : ∀ k, (left group k).Fits s) (hstack : rho.length < 1006)
    (hrun : s.halt = .Running) :
    StackRoundTrace.runInstrSeq (leftCode group)
        (stateAt s pc w (StackRoundTemplate.mask :: rho)) =
      some (stateAt s (StackRoundTrace.pcAfter pc (leftCode group))
        (fourResult (left group) s w) (StackRoundTemplate.mask :: rho)) :=
  run_left_four (left group) s pc w rho hfit hstack hrun

theorem run_rightCode (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hfit : ∀ k, (right k).Fits s) (hstack : rho.length < 1001)
    (hrun : s.halt = .Running) :
    StackRoundTrace.runInstrSeq rightCode
        (stateAt s pc w (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho)) =
      some (stateAt s (StackRoundTrace.pcAfter pc rightCode)
        (fourResult right s w) (a :: b :: c :: d :: e :: StackRoundTemplate.mask :: rho)) :=
  run_right_four right s pc w a b c d e rho hfit hstack hrun

#print axioms left_fits
#print axioms left_result_after
#print axioms right_result_after64
#print axioms run_leftCode
#print axioms run_rightCode

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskParams
