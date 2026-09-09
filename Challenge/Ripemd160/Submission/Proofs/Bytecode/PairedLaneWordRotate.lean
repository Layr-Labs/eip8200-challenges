import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordBlend
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneRoundSemantic

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRotate

open EvmSemantics PairedLaneProduct PairedLaneRoundSemantic
open PairedLaneUInt256Bridge PairedLaneWordBlend PairedLaneWordBoolean PairedLaneScaledRotate

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

/-- `x + (x & mask) * (2^d - 1)`, in the operand order the bytecode evaluates. -/
def wordScale (x mask : UInt256) (d : Nat) : UInt256 :=
  UInt256.add (UInt256.mul (UInt256.ofNat (2 ^ d - 1)) (UInt256.land mask x)) x

theorem bits_wordScale_lower (x : UInt256) (d : Nat) :
    bits (wordScale x lowerWord d) = scaleLow (bits x) d := by
  simp only [wordScale, scaleLow, bits_add, bits_mul, bits_land, bits_ofNat, lowerWord, bits_word]

theorem bits_wordScale_upper (x : UInt256) (d : Nat) :
    bits (wordScale x upperWord d) = scaleHigh (bits x) d := by
  simp only [wordScale, scaleHigh, bits_add, bits_mul, bits_land, bits_ofNat, upperWord, bits_word]

#print axioms bits_wordScale_lower
#print axioms bits_wordScale_upper

def wordRotate (x : UInt256) (r s : Nat) : UInt256 :=
  if r = s then wordShift x (32 - r)
  else if s < r then wordShift (wordScale x lowerWord (r - s)) (32 - s)
  else wordShift (wordScale x upperWord (s - r)) (32 - r)

theorem bits_wordRotate (x : UInt256) (r s : Nat) :
    bits (wordRotate x r s) = rawRotate (bits x) r s := by
  have hr : 32 - r < 256 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  have hs : 32 - s < 256 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  by_cases h : r = s
  · simp only [wordRotate, rawRotate, if_pos h]
    exact bits_wordShift x (32 - r) hr
  · by_cases hlt : s < r
    · simp only [wordRotate, rawRotate, if_neg h, if_pos hlt]
      rw [bits_wordShift _ _ hs, bits_wordScale_lower]
    · simp only [wordRotate, rawRotate, if_neg h, if_neg hlt]
      rw [bits_wordShift _ _ hr, bits_wordScale_upper]

#print axioms bits_wordRotate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneWordRotate
