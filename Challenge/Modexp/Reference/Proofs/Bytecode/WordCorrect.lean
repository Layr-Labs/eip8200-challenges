import Challenge.Modexp.Reference.Proofs.Bytecode.WordExit
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Correctness of the one-word MODEXP arithmetic

The bytecode uses a branchless square-and-multiply update.  These lemmas
bridge its `UInt256` bitwise expression to ordinary modular arithmetic and
then to the padded EIP-198 exponent parser.
-/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.WordCorrect

open EvmSemantics
open EvmSemantics.EVM
open Word
open WordLoops
open WordExit

theorem land_toNat (a b : UInt256) :
    (UInt256.land a b).toNat = (a.toNat &&& b.toNat) := by
  cases a with | mk a =>
  cases b with | mk b =>
  simp only [UInt256.land, UInt256.toNat]
  unfold Fin.land
  simp only
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left a.isLt)

theorem xor_toNat (a b : UInt256) :
    (UInt256.xor a b).toNat = (a.toNat ^^^ b.toNat) := by
  cases a with | mk a =>
  cases b with | mk b =>
  simp only [UInt256.xor, UInt256.toNat]
  unfold Fin.xor
  simp only
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow a.isLt b.isLt)

theorem ofNat_toNat (a : UInt256) : UInt256.ofNat a.toNat = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt a.val.isLt

theorem select_zero (x y : UInt256) :
    UInt256.xor x (UInt256.land (UInt256.xor x y)
      (UInt256.ofNat 0 - UInt256.ofNat 0)) = x := by
  apply Challenge.EvmProof.Word.word_ext
  rw [xor_toNat, land_toNat, xor_toNat]
  have hmask : UInt256.ofNat 0 - UInt256.ofNat 0 = UInt256.ofNat 0 := by
    decide
  rw [hmask, Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num

theorem select_one (x y : UInt256) :
    UInt256.xor x (UInt256.land (UInt256.xor x y)
      (UInt256.ofNat 0 - UInt256.ofNat 1)) = y := by
  apply Challenge.EvmProof.Word.word_ext
  rw [xor_toNat, land_toNat, xor_toNat]
  have hmask : UInt256.ofNat 0 - UInt256.ofNat 1 =
      UInt256.ofNat (2 ^ 256 - 1) := by decide
  rw [hmask, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 2 ^ 256 - 1 < 2 ^ 256),
    Nat.and_two_pow_sub_one_eq_mod]
  have hxor : (x.toNat ^^^ y.toNat) % 2 ^ 256 = x.toNat ^^^ y.toNat :=
    Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.val.isLt y.val.isLt)
  rw [hxor, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

def exponentBitNat (byte : UInt256) (j : Nat) : Nat :=
  (byte.toNat >>> (7 - j)) % 2

theorem exponentBit_eq (byte : UInt256) (j : Nat) (hj : j < 8) :
    exponentBit byte j = UInt256.ofNat (exponentBitNat byte j) := by
  have hshift := Challenge.EvmProof.Word.shiftRight_ofNat
    (value := byte.toNat) (shift := 7 - j) byte.val.isLt (by omega)
  have hword := ofNat_toNat byte
  calc
    exponentBit byte j = UInt256.land
        (UInt256.ofNat (byte.toNat >>> (7 - j))) (UInt256.ofNat 1) := by
      unfold exponentBit
      rw [show UInt256.shiftRight byte (UInt256.ofNat (7 - j)) =
          UInt256.ofNat (byte.toNat >>> (7 - j)) by
        calc
          UInt256.shiftRight byte (UInt256.ofNat (7 - j)) =
              UInt256.shiftRight (UInt256.ofNat byte.toNat)
                (UInt256.ofNat (7 - j)) := by rw [hword]
          _ = UInt256.ofNat (byte.toNat >>> (7 - j)) := hshift]
    _ = UInt256.ofNat (exponentBitNat byte j) := by
      apply Challenge.EvmProof.Word.word_ext
      unfold exponentBitNat
      rw [land_toNat, Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat]
      have hsrmod : (byte.toNat >>> (7 - j)) % 2 ^ 256 =
          byte.toNat >>> (7 - j) := Nat.mod_eq_of_lt
            (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) byte.val.isLt)
      have h1mod : 1 % 2 ^ 256 = 1 :=
        Nat.mod_eq_of_lt (by norm_num)
      simp only [hsrmod, h1mod]
      change ((byte.toNat >>> (7 - j)) &&& 1) =
        ((byte.toNat >>> (7 - j)) % 2) % 2 ^ 256
      rw [show (1 : Nat) = 2 ^ 1 - 1 by norm_num,
        Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt
          (by omega : (byte.toNat >>> (7 - j)) % 2 < 2 ^ 256)]

theorem exponentBitNat_zero_or_one (byte : UInt256) (j : Nat) :
    exponentBitNat byte j = 0 ∨ exponentBitNat byte j = 1 := by
  unfold exponentBitNat
  omega

theorem mulMod_toNat (a b : UInt256) (modulus : Nat)
    (hmodpos : 0 < modulus) (hmodlt : modulus < 2 ^ 256) :
    (UInt256.mulMod a b (UInt256.ofNat modulus)).toNat =
      (a.toNat * b.toNat) % modulus := by
  unfold UInt256.mulMod
  have hmword : (UInt256.ofNat modulus).val.val ≠ 0 := by
    change (UInt256.ofNat modulus).toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hmodlt]
    omega
  rw [if_neg hmword, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hmodlt,
    Nat.mod_eq_of_lt ((Nat.mod_lt _ hmodpos).trans hmodlt)]

theorem mulMod_ofNat (a b modulus : Nat)
    (hmodpos : 0 < modulus) (hmodlt : modulus < 2 ^ 256)
    (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    UInt256.mulMod (UInt256.ofNat a) (UInt256.ofNat b)
        (UInt256.ofNat modulus) =
      UInt256.ofNat ((a * b) % modulus) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [mulMod_toNat _ _ modulus hmodpos hmodlt,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt ((Nat.mod_lt _ hmodpos).trans hmodlt)]

theorem bitStep_eq_zero (input : ByteArray) (byte : UInt256) (j : Nat)
    (acc base : UInt256) (hbit : exponentBitNat byte j = 0)
    (hj : j < 8) :
    bitStep input byte j acc base =
      UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)) := by
  unfold bitStep
  rw [exponentBit_eq byte j hj, hbit]
  exact select_zero _ _

theorem bitStep_eq_one (input : ByteArray) (byte : UInt256) (j : Nat)
    (acc base : UInt256) (hbit : exponentBitNat byte j = 1)
    (hj : j < 8) :
    bitStep input byte j acc base =
      UInt256.mulMod
        (UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input))) base
        (UInt256.ofNat (modulusValue input)) := by
  unfold bitStep
  rw [exponentBit_eq byte j hj, hbit]
  exact select_one _ _

end Challenge.Modexp.Reference.Proofs.Bytecode.WordCorrect
