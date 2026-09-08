import EvmSemantics.Data.UInt256
import Init.Data.BitVec.Lemmas
import Init.Data.Fin.Bitwise

set_option warningAsError true

/-! Representation-only connection to the canonical EVM word operations.
All input words are arbitrary; only the shift count is bounded below 256. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge

open EvmSemantics

def bits (value : UInt256) : BitVec 256 := BitVec.ofFin value.val
def word (value : BitVec 256) : UInt256 := ⟨value.toFin⟩

theorem bits_word (value : BitVec 256) : bits (word value) = value := rfl

theorem word_bits (value : UInt256) : word (bits value) = value := rfl

theorem bits_injective : Function.Injective bits := by
  intro a b h
  exact congrArg word h

theorem bits_toNat (value : UInt256) : (bits value).toNat = value.toNat := rfl

theorem bits_ofNat (value : Nat) :
    bits (UInt256.ofNat value) = BitVec.ofNat 256 value := rfl

theorem bits_add (a b : UInt256) :
    bits (UInt256.add a b) = bits a + bits b := rfl

theorem bits_mul (a b : UInt256) :
    bits (UInt256.mul a b) = bits a * bits b := rfl

theorem bits_land (a b : UInt256) :
    bits (UInt256.land a b) = bits a &&& bits b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  exact Fin.and_val a.val b.val

theorem bits_lor (a b : UInt256) :
    bits (UInt256.lor a b) = bits a ||| bits b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]
  exact Fin.or_val_of_two_pow a.val b.val

theorem bits_xor (a b : UInt256) :
    bits (UInt256.xor a b) = bits a ^^^ bits b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor]
  exact Fin.xor_val_of_two_pow a.val b.val

theorem bits_lnot (a : UInt256) :
    bits (UInt256.lnot a) = ~~~bits a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_not]
  change (2 ^ 256 - 1 - a.toNat) % 2 ^ 256 = 2 ^ 256 - 1 - a.toNat
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)

theorem small_shift_toNat (n : Nat) (hn : n < 256) :
    (UInt256.ofNat n).toNat = n := by
  change n % (2 ^ 256) = n
  exact Nat.mod_eq_of_lt (Nat.lt_trans hn (by decide))

theorem bits_shr (a : UInt256) (n : Nat) (hn : n < 256) :
    bits (UInt256.shiftRight a (UInt256.ofNat n)) = bits a >>> n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight]
  have hcount := small_shift_toNat n hn
  unfold UInt256.shiftRight
  rw [hcount, if_neg (Nat.not_le_of_lt hn)]
  change (a.val >>> (UInt256.ofNat n).val).val = a.toNat >>> n
  rw [Fin.shiftRight_val]
  exact congrArg (fun count => a.toNat >>> count) hcount

theorem bits_shl (a : UInt256) (n : Nat) (hn : n < 256) :
    bits (UInt256.shiftLeft a (UInt256.ofNat n)) = bits a <<< n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft]
  have hcount := small_shift_toNat n hn
  unfold UInt256.shiftLeft
  rw [hcount, if_neg (Nat.not_le_of_lt hn)]
  change (a.toNat <<< n) % 2 ^ 256 % 2 ^ 256 = (a.toNat <<< n) % 2 ^ 256
  exact Nat.mod_mod _ _

#print axioms bits_word
#print axioms word_bits
#print axioms bits_injective
#print axioms bits_toNat
#print axioms bits_ofNat
#print axioms bits_add
#print axioms bits_mul
#print axioms bits_land
#print axioms bits_lor
#print axioms bits_xor
#print axioms bits_lnot
#print axioms small_shift_toNat
#print axioms bits_shr
#print axioms bits_shl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge
