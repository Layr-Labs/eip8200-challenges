import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordBlend
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneRoundSemantic

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRotate

open EvmSemantics PairedLaneProduct PairedLaneRoundSemantic
open PairedLaneUInt256Bridge PairedLaneWordBlend

theorem bits_productShift (x c : UInt256) (n : Nat) (hn : n < 256) :
    bits (UInt256.shiftRight (UInt256.mul x c) (UInt256.ofNat n)) =
      (bits x * bits c) >>> n :=
  (bits_shr (UInt256.mul x c) n hn).trans
    (congrArg (fun z : BitVec 256 => z >>> n) (bits_mul x c))

#print axioms bits_productShift

def factorWord : UInt256 := word factor

def wordShift (x : UInt256) (n : Nat) : UInt256 :=
  UInt256.shiftRight (UInt256.mul x factorWord) (UInt256.ofNat n)

theorem bits_wordShift (x : UInt256) (n : Nat) (hn : n < 256) :
    bits (wordShift x n) = (bits x * factor) >>> n :=
  (bits_productShift x factorWord n hn).trans
    (congrArg (fun z : BitVec 256 => (bits x * z) >>> n) (bits_word factor))

#print axioms bits_wordShift

def wordRotate (x : UInt256) (r s : Nat) : UInt256 :=
  if r = s then wordShift x (32 - r)
  else wordBlend (wordShift x (32 - r)) (wordShift x (32 - s))

theorem bits_wordRotate (x : UInt256) (r s : Nat) :
    bits (wordRotate x r s) = rawRotate (bits x) r s := by
  have hr : 32 - r < 256 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  have hs : 32 - s < 256 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  by_cases h : r = s
  · simp only [wordRotate, rawRotate, if_pos h]
    exact bits_wordShift x (32 - r) hr
  · simp only [wordRotate, rawRotate, if_neg h]
    exact (bits_wordBlend (wordShift x (32 - r)) (wordShift x (32 - s))).trans
      (congr (congrArg PairedLaneCarry.blend (bits_wordShift x (32 - r) hr))
        (bits_wordShift x (32 - s) hs))

#print axioms bits_wordRotate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRotate
