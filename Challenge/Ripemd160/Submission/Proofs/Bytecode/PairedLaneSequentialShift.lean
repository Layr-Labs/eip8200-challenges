import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneSequentialShift

open EvmSemantics PairedLaneUInt256Bridge

/-- Sequential logical shifts add their counts, for every raw bit word. -/
theorem shr_bits (p : BitVec w) (a b : Nat) :
    (p >>> a) >>> b = p >>> (a + b) :=
  (BitVec.shiftRight_add p a b).symm

#print axioms shr_bits

theorem shr_word (p : UInt256) (a b : Nat) (h : a + b < 256) :
    UInt256.shiftRight (UInt256.shiftRight p (UInt256.ofNat a)) (UInt256.ofNat b) =
      UInt256.shiftRight p (UInt256.ofNat (a + b)) := by
  have ha : a < 256 := Nat.lt_of_le_of_lt (Nat.le_add_right a b) h
  have hb : b < 256 := Nat.lt_of_le_of_lt (Nat.le_add_left b a) h
  apply bits_injective
  rw [bits_shr _ b hb, bits_shr p a ha, bits_shr p (a + b) h]
  exact shr_bits _ _ _

#print axioms shr_word

/-- Only the statically known shift counts are ordered; the value stays arbitrary. -/
theorem shr_difference (p : UInt256) (a b : Nat) (hab : a ≤ b) (hb : b < 256) :
    UInt256.shiftRight (UInt256.shiftRight p (UInt256.ofNat a)) (UInt256.ofNat (b - a)) =
      UInt256.shiftRight p (UInt256.ofNat b) := by
  have hsum : a + (b - a) = b := Nat.add_sub_of_le hab
  have hbound : a + (b - a) < 256 := hsum.symm ▸ hb
  exact (shr_word p a (b-a) hbound).trans
    (congrArg (fun n => UInt256.shiftRight p (UInt256.ofNat n)) hsum)

#print axioms shr_difference

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneSequentialShift
