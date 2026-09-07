import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskQuadGroup

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineParams
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open CavityQuadGroup QuadSemantic StackCompression

def left4 (word : Nat → UInt32) (k : Fin 20) (w : Compression.EvmWorking) :=
  leftStep word (quadIndex k 3) (leftStep word (quadIndex k 2)
    (leftStep word (quadIndex k 1) (leftStep word (quadIndex k 0) w)))
def right4 (word : Nat → UInt32) (k : Fin 20) (w : Compression.EvmWorking) :=
  rightStep word (quadIndex k 3) (rightStep word (quadIndex k 2)
    (rightStep word (quadIndex k 1) (rightStep word (quadIndex k 0) w)))

def left (k : Fin 20) : Params where
  function := ⟨k.val / 4, by omega⟩
  address := quadLeftAddress k
  rotation := quadLeftRotation k
  constant := quadLeftConstant k
  rotations_bounded := quadLeftRotation_le_32 k
  constant_zero h := by fin_cases k <;> first | rfl | contradiction

def right (k : Fin 20) : Params where
  function := ⟨4 - k.val / 4, by omega⟩
  address := quadRightAddress k
  rotation := quadRightRotation k
  constant := quadRightConstant k
  rotations_bounded := quadRightRotation_le_32 k
  constant_zero h := by fin_cases k <;> first | rfl | contradiction

theorem left_fits (s : State) (k : Fin 20) (h : 39 ≤ s.activeWords.toNat) :
    (left k).Fits s := fun i => quadLeftAddress_end_le s k i h

theorem right_fits (s : State) (k : Fin 20) (h : 39 ≤ s.activeWords.toNat) :
    (right k).Fits s := fun i => quadRightAddress_end_le s k i h

theorem left_apply (s : State) (word : Nat → UInt32) (w : Compression.EvmWorking)
    (k : Fin 20) (h : DenseWordsAt s word) : (left k).apply s w = left4 word k w := by
  have e := quadWorking_left s word w k h
  fin_cases k <;> exact e

theorem right_apply (s : State) (word : Nat → UInt32) (w : Compression.EvmWorking)
    (k : Fin 20) (h : DenseWordsAt s word) : (right k).apply s w = right4 word k w := by
  have e := quadWorking_right s word w k h
  fin_cases k <;> exact e

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FullInlineParams
