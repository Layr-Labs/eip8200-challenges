import Challenge.Modexp.Submission.Proofs.Bytecode.WordLoopFinish
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# The multiplier the unrolled copies use

The copies compute `mulmod (acc * acc) (1 + (base - 1) * bit) m` in one further
`MULMOD`, which is the same accumulator the mask select produced: the
multiplier is `1` when the bit is clear and the base when it is set.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordBitSel

open EvmSemantics
open EvmSemantics.EVM
open Word

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


theorem word_toNat_mul (a b : UInt256) :
    (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

theorem word_mul_zero (a : UInt256) : a * UInt256.ofNat 0 = UInt256.ofNat 0 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [word_toNat_mul, Challenge.EvmProof.Word.word_toNat_ofNat]
  simp

theorem word_mul_one (a : UInt256) : a * UInt256.ofNat 1 = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [word_toNat_mul, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256), Nat.mul_one]
  exact Nat.mod_eq_of_lt a.val.isLt

theorem word_add_zero_one : UInt256.ofNat 1 + UInt256.ofNat 0 = UInt256.ofNat 1 := by
  decide

theorem word_one_add_sub_one (a : UInt256) :
    UInt256.ofNat 1 + (a - UInt256.ofNat 1) = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256)]
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  omega

theorem mulMod_lt (a b m : UInt256) (hm : 0 < m.toNat) :
    (UInt256.mulMod a b m).toNat < m.toNat := by
  have hmne : m.val.val ≠ 0 := by
    change m.toNat ≠ 0
    omega
  have h1 : a.toNat * b.toNat % m.toNat < m.toNat := Nat.mod_lt _ hm
  have h2 : m.toNat < 2 ^ 256 := m.val.isLt
  unfold UInt256.mulMod
  rw [if_neg hmne, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans h1 h2)]
  exact h1

theorem mulMod_one_right (x m : UInt256) (hx : x.toNat < m.toNat) :
    UInt256.mulMod x (UInt256.ofNat 1) m = x := by
  have hmne : m.val.val ≠ 0 := by
    change m.toNat ≠ 0
    omega
  unfold UInt256.mulMod
  rw [if_neg hmne]
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256), Nat.mul_one,
    Nat.mod_eq_of_lt hx]
  exact Nat.mod_eq_of_lt x.val.isLt

theorem mulMod_mulMod_one (a m : UInt256) :
    UInt256.mulMod (UInt256.mulMod a a m) (UInt256.ofNat 1) m
      = UInt256.mulMod a a m := by
  by_cases hm : m.toNat = 0
  · have h : m.val.val = 0 := hm
    unfold UInt256.mulMod
    simp [h]
  · exact mulMod_one_right _ m (mulMod_lt a a m (by omega))

/-- The multiplier select and the mask select agree. -/
theorem bitStepSel_eq (input : ByteArray) (byte : UInt256) (j : Nat)
    (acc base : UInt256) (hj : j < 8) :
    bitStepSel input byte j acc base = bitStep input byte j acc base := by
  rcases exponentBitNat_zero_or_one byte j with hbit | hbit
  · unfold bitStepSel bitStep
    rw [exponentBit_eq byte j hj, hbit]
    show UInt256.mulMod (UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)))
        (UInt256.ofNat 1 + (base - UInt256.ofNat 1) * UInt256.ofNat 0)
        (UInt256.ofNat (modulusValue input))
      = UInt256.xor (UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)))
          (UInt256.land (UInt256.xor
            (UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)))
            (UInt256.mulMod (UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)))
              base (UInt256.ofNat (modulusValue input))))
            (UInt256.ofNat 0 - UInt256.ofNat 0))
    rw [word_mul_zero, word_add_zero_one, mulMod_mulMod_one, select_zero]
  · unfold bitStepSel bitStep
    rw [exponentBit_eq byte j hj, hbit]
    show UInt256.mulMod (UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)))
        (UInt256.ofNat 1 + (base - UInt256.ofNat 1) * UInt256.ofNat 1)
        (UInt256.ofNat (modulusValue input))
      = UInt256.xor (UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)))
          (UInt256.land (UInt256.xor
            (UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)))
            (UInt256.mulMod (UInt256.mulMod acc acc (UInt256.ofNat (modulusValue input)))
              base (UInt256.ofNat (modulusValue input))))
            (UInt256.ofNat 0 - UInt256.ofNat 1))
    rw [word_mul_one, word_one_add_sub_one, select_one]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordBitSel
