import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Product
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordScale
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Carry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Nat
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Core

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RootCommonFactorPlusProduct

open Paired144Nat Paired144Core

private theorem low_shift_nat (x : BitVec 256) (n : Nat) :
    (low (x >>> n)).toNat = x.toNat / 2 ^ n % 2 ^ 32 := by
  simp only [low, BitVec.extractLsb'_toNat, Nat.pow_zero, Nat.div_one,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem high_shift_nat (x : BitVec 256) (n : Nat) :
    (high (x >>> n)).toNat = x.toNat / 2 ^ (n + 144) % 2 ^ 32 := by
  simp only [high, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]

def coefficient : BitVec 256 := BitVec.ofNat 256 ((2 ^ 32 + 1) * (2 ^ 1 + 2 ^ 65))

def scaled (a b : BitVec 32) (u v : Nat) : BitVec 256 :=
  (BitVec.ofNat 256 a.toNat <<< u) + (BitVec.ofNat 256 b.toNat <<< (144 + v))

def rawProduct (a b : BitVec 32) (u v : Nat) : BitVec 256 :=
  scaled a b u v * coefficient

def natProduct (a b u v : Nat) : Nat :=
  (a * 2 ^ u + b * 2 ^ (144 + v)) * ((2 ^ 32 + 1) * (2 ^ 1 + 2 ^ 65))

def lowChunk (a u : Nat) : Nat := a * (2 ^ 32 + 1) * 2 ^ u * (2 ^ 1 + 2 ^ 65)

def highChunk (b v : Nat) : Nat := b * (2 ^ 32 + 1) * 2 ^ v * (1 + 2 ^ 64)

private theorem shifted_mul_toNat (a b : BitVec 32) (c : BitVec 256) (u v : Nat) :
    (((BitVec.ofNat 256 a.toNat <<< u) +
      (BitVec.ofNat 256 b.toNat <<< v)) * c).toNat =
      ((a.toNat * 2 ^ u + b.toNat * 2 ^ v) * c.toNat) % 2 ^ 256 := by
  simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.add_mod_mod, Nat.mod_add_mod,
    Nat.mod_mul_mod]

private theorem coefficient_toNat : coefficient.toNat = (2 ^ 32 + 1) * (2 ^ 1 + 2 ^ 65) := by
  decide

theorem rawProduct_toNat (a b : BitVec 32) (u v : Nat) :
    (rawProduct a b u v).toNat = natProduct a.toNat b.toNat u v % 2 ^ 256 := by
  unfold rawProduct scaled
  rw [shifted_mul_toNat, coefficient_toNat]
  rfl

theorem natProduct_chunks (a b u v : Nat) :
    natProduct a b u v = lowChunk a u + highChunk b v * 2 ^ 145 := by
  unfold natProduct lowChunk highChunk
  rw [Nat.add_mul]
  refine congr (congrArg Nat.add ?_) ?_
  · ac_rfl
  · rw [Nat.pow_add]
    have hc : 2 ^ 144 * (2 ^ 32 + 1) * (2 ^ 1 + 2 ^ 65) =
        (2 ^ 32 + 1) * (1 + 2 ^ 64) * 2 ^ 145 := by decide
    calc
      _ = (b * 2 ^ v) * (2 ^ 144 * (2 ^ 32 + 1) * (2 ^ 1 + 2 ^ 65)) := by ac_rfl
      _ = (b * 2 ^ v) * ((2 ^ 32 + 1) * (1 + 2 ^ 64) * 2 ^ 145) := by rw [hc]
      _ = _ := by ac_rfl

theorem lowChunk_lt (a : BitVec 32) (u : Nat) (hu : u ≤ 10) :
    lowChunk a.toNat u < 2 ^ 144 := by
  have ha : a.toNat ≤ 2 ^ 32 - 1 := Nat.le_sub_one_of_lt a.isLt
  have hp : 2 ^ u ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hu
  calc
    lowChunk a.toNat u ≤ (2 ^ 32 - 1) * (2 ^ 32 + 1) * 2 ^ 10 * (2 ^ 1 + 2 ^ 65) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_right _ ha) hp)
    _ < 2 ^ 144 := by decide

private theorem gap144_of_residue (x : BitVec 256) (y : Nat)
    (hmod : x.toNat % 2 ^ 145 = y) (hy : y < 2 ^ 144) : x.getLsbD 144 = false := by
  rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  apply decide_eq_false_iff_not.mpr
  simp only [Nat.reducePow] at *
  omega

theorem rawProduct_gap144 (a b : BitVec 32) (u v : Nat) (hu : u ≤ 10) :
    (rawProduct a b u v).getLsbD 144 = false := by
  have hlow := lowChunk_lt a u hu
  have hmod : (rawProduct a b u v).toNat % 2 ^ 145 = lowChunk a.toNat u := by
    rw [rawProduct_toNat, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 145 ≤ 256)),
      natProduct_chunks, mod_pow_add_mul_pow _ _ 145 145 (by decide)]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hlow (by decide))
  exact gap144_of_residue _ _ hmod hlow

theorem shiftedProduct_gap (a b : BitVec 32) (u v n : Nat)
    (hu : u ≤ 10) (hn : n ≤ 144) :
    (rawProduct a b u v >>> n).getLsbD (144 - n) = false := by
  rw [BitVec.getLsbD_ushiftRight]
  have hindex : n + (144 - n) = 144 := by omega
  rw [hindex]
  exact rawProduct_gap144 a b u v hu

theorem low_shift_toNat (a b : BitVec 32) (u v n : Nat)
    (hu : u ≤ 10) (hn0 : 18 ≤ n) (hn : n ≤ 28) :
    (low (rawProduct a b u v >>> n)).toNat =
      a.toNat * (2 ^ 32 + 1) / 2 ^ (n - 1 - u) % 2 ^ 32 := by
  rw [low_shift_nat]
  rw [rawProduct_toNat, truncate_window _ n 32 256 (by omega), natProduct_chunks,
    div_pow_add_mul_pow _ _ n 145 (by omega), mod_pow_add_mul_pow _ _ _ 32 (by omega)]
  unfold lowChunk
  rw [Nat.mul_add, div_pow_add_mul_pow _ _ n 65 (by omega),
    mod_pow_add_mul_pow _ _ _ 32 (by omega), mul_pow_div_pow _ 1 n (by omega),
    mul_pow_div_pow _ u (n - 1) (by omega)]

theorem high_shift_toNat (a b : BitVec 32) (u v n : Nat)
    (hu : u ≤ 10) (hv : v ≤ 10) (hn0 : 18 ≤ n) (hn : n ≤ 28) :
    (high (rawProduct a b u v >>> n)).toNat =
      b.toNat * (2 ^ 32 + 1) / 2 ^ (n - 1 - v) % 2 ^ 32 := by
  rw [high_shift_nat]
  rw [rawProduct_toNat, truncate_window _ (n + 144) 32 256 (by omega), natProduct_chunks]
  have he : n + 144 = 145 + (n - 1) := by omega
  rw [he, div_pow_add_mul_pow_of_lt _ _ (n - 1) 145
    (Nat.lt_trans (lowChunk_lt a u hu) (by decide))]
  unfold highChunk
  rw [Nat.mul_add, Nat.mul_one, div_pow_add_mul_pow _ _ (n - 1) 64 (by omega),
    mod_pow_add_mul_pow _ _ _ 32 (by omega), mul_pow_div_pow _ v (n - 1) (by omega)]

#print axioms rawProduct_toNat
#print axioms rawProduct_gap144
#print axioms shiftedProduct_gap
#print axioms low_shift_toNat
#print axioms high_shift_toNat

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RootCommonFactorPlusProduct


set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RootCommonFactorPlusRotation

open Paired144Core Paired144Nat RootCommonFactorPlusProduct

def rawRotate (a b : BitVec 32) (r s : Nat) : BitVec 256 :=
  rawProduct a b (r - s) (s - r) >>> (33 - min r s)

theorem low_rotate (a b : BitVec 32) (r s : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15) (hs0 : 5 ≤ s) (hs : s ≤ 15) :
    low (rawRotate a b r s) = a.rotateLeft r := by
  apply BitVec.eq_of_toNat_eq
  rw [rawRotate, low_shift_toNat a b (r - s) (s - r) (33 - min r s)
    (by omega) (by omega) (by omega), rotate_toNat a r (by omega) (by omega)]
  have he : 33 - min r s - 1 - (r - s) = 32 - r := by omega
  rw [he]

theorem high_rotate (a b : BitVec 32) (r s : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15) (hs0 : 5 ≤ s) (hs : s ≤ 15) :
    high (rawRotate a b r s) = b.rotateLeft s := by
  apply BitVec.eq_of_toNat_eq
  rw [rawRotate, high_shift_toNat a b (r - s) (s - r) (33 - min r s)
    (by omega) (by omega) (by omega) (by omega), rotate_toNat b s (by omega) (by omega)]
  have he : 33 - min r s - 1 - (s - r) = 32 - s := by omega
  rw [he]

theorem rawRotate_gap (a b : BitVec 32) (r s : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15) (hs0 : 5 ≤ s) (hs : s ≤ 15) :
    (rawRotate a b r s).getLsbD (144 - (33 - min r s)) = false := by
  exact shiftedProduct_gap a b (r - s) (s - r) (33 - min r s) (by omega) (by omega)

theorem normalize_rotate (a b : BitVec 32) (r s : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15) (hs0 : 5 ≤ s) (hs : s ≤ 15) :
    normalize (rawRotate a b r s) = pack (a.rotateLeft r) (b.rotateLeft s) := by
  rw [normalize, low_rotate a b r s hr0 hr hs0 hs, high_rotate a b r s hr0 hr hs0 hs]

/-- Arbitrary scalar E addends are included in the machine identity. The
legacy product's own bit144 separator blocks carry into the high lane. -/
theorem normalize_rotate_add (a b e f : BitVec 32) (r s : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15) (hs0 : 5 ≤ s) (hs : s ≤ 15) :
    normalize (rawRotate a b r s + pack e f) =
      pack (a.rotateLeft r + e) (b.rotateLeft s + f) := by
  rw [Paired144Carry.normalize_add_pack _ e f (144 - (33 - min r s))
    (by omega) (by omega) (rawRotate_gap a b r s hr0 hr hs0 hs),
    low_rotate a b r s hr0 hr hs0 hs, high_rotate a b r s hr0 hr hs0 hs]

theorem normalize_cRotate (a b : BitVec 32) :
    normalize (rawProduct a b 0 0 >>> 23) = pack (a.rotateLeft 10) (b.rotateLeft 10) := by
  exact normalize_rotate a b 10 10 (by decide) (by decide) (by decide) (by decide)

#print axioms low_rotate
#print axioms high_rotate
#print axioms rawRotate_gap
#print axioms normalize_rotate
#print axioms normalize_rotate_add
#print axioms normalize_cRotate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RootCommonFactorPlusRotation

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RootCommonFactorPlusWord
open EvmSemantics Paired144Core PairedLaneUInt256Bridge
open RootCommonFactorPlusProduct RootCommonFactorPlusRotation

def factorWord : UInt256 := UInt256.ofNat ((2 ^ 32 + 1) * (2 + 2 ^ 65))
def wordShift (x : UInt256) (n : Nat) : UInt256 :=
  UInt256.shiftRight (UInt256.mul x factorWord) (UInt256.ofNat n)

theorem factor_alias : factorWord = Paired144WordRound.fusedCoefficientWord 1 0 := by decide

theorem factor_bits : bits factorWord = coefficient := by decide

theorem bits_wordShift (x : UInt256) (n : Nat) (hn : n < 256) :
    bits (wordShift x n) = (bits x * coefficient) >>> n := by
  rw [wordShift, bits_shr _ n hn, bits_mul, factor_bits]

theorem scaled_zero (a b : BitVec 32) : scaled a b 0 0 = pack a b := by
  change Paired144LegacyProduct.scaled a b 0 0 = pack a b
  rw [← Paired144WordScale.scaleLow_eq_scaled a b 0 (by decide)]
  simp only [Paired144WordScale.scaleLow, Nat.pow_zero, Nat.sub_self,
    BitVec.zero_mul, BitVec.zero_add]

def wordLegacy (x : UInt256) (r s : Nat) : UInt256 :=
  let y := UInt256.land x Paired144WordRound.pairWord
  if r = s then wordShift y (33 - r)
  else if s < r then
    wordShift (Paired144WordRound.wordScale y Paired144WordRound.lowerWord (r-s)) (33-s)
  else wordShift (Paired144WordRound.wordScale y Paired144WordRound.upperWord (s-r)) (33-r)

theorem bits_wordLegacy (x : UInt256) (a b : BitVec 32) (r s : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15) (hs0 : 5 ≤ s) (hs : s ≤ 15)
    (hn : normalize (bits x) = pack a b) :
    bits (wordLegacy x r s) = rawRotate a b r s := by
  have hx : UInt256.land x Paired144WordRound.pairWord = word (pack a b) := by
    apply bits_injective
    simpa only [bits_land, Paired144WordRound.pairWord, bits_word,
      ← normalize_eq_and] using hn
  rw [wordLegacy, hx]
  by_cases he : r=s
  · subst s
    rw [if_pos rfl, bits_wordShift _ _ (by omega), bits_word]
    simp only [rawRotate, rawProduct, Nat.sub_self, Nat.min_self, scaled_zero]
  · rw [if_neg he]
    by_cases hlt : s<r
    · rw [if_pos hlt, bits_wordShift _ _ (by omega),
        Paired144WordScale.bits_wordScale_lower a b (r-s) (by omega)]
      simp only [rawRotate, rawProduct, scaled, Paired144LegacyProduct.scaled,
        Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt), Nat.min_eq_right (Nat.le_of_lt hlt)]
    · rw [if_neg hlt, bits_wordShift _ _ (by omega),
        Paired144WordScale.bits_wordScale_upper a b (s-r) (by omega)]
      have hle : r≤s := by omega
      simp only [rawRotate, rawProduct, scaled, Paired144LegacyProduct.scaled,
        Nat.sub_eq_zero_of_le hle, Nat.min_eq_left hle]

theorem normalize_wordLegacy_add (x : UInt256) (a b e f : BitVec 32) (r s : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15) (hs0 : 5 ≤ s) (hs : s ≤ 15)
    (hn : normalize (bits x) = pack a b) :
    normalize (bits (wordLegacy x r s) + pack e f) =
      pack (a.rotateLeft r+e) (b.rotateLeft s+f) := by
  rw [bits_wordLegacy x a b r s hr0 hr hs0 hs hn]
  exact normalize_rotate_add a b e f r s hr0 hr hs0 hs

theorem normalize_equal_add (x : UInt256) (a b e f : BitVec 32) (r : Nat)
    (hr0 : 5 ≤ r) (hr : r ≤ 15)
    (hn : normalize (bits x) = pack a b) :
    normalize (bits (wordShift (UInt256.land x Paired144WordRound.pairWord) (33-r)) +
      pack e f) = pack (a.rotateLeft r+e) (b.rotateLeft r+f) := by
  simpa [wordLegacy] using
    normalize_wordLegacy_add x a b e f r r hr0 hr hr0 hr hn

theorem normalize_cRotate (a b : BitVec 32) :
    normalize (bits (wordShift (word (pack a b)) 23)) =
      pack (a.rotateLeft 10) (b.rotateLeft 10) := by
  rw [bits_wordShift _ _ (by decide), bits_word, ← scaled_zero a b]
  exact RootCommonFactorPlusRotation.normalize_cRotate a b

theorem cRotate_gap121 (a b : BitVec 32) :
    (bits (wordShift (word (pack a b)) 23)).getLsbD 121 = false := by
  rw [bits_wordShift _ _ (by decide), bits_word, ← scaled_zero a b]
  exact shiftedProduct_gap a b 0 0 23 (by decide) (by decide)

#print axioms factor_alias
#print axioms bits_wordLegacy
#print axioms normalize_wordLegacy_add
#print axioms normalize_equal_add
#print axioms normalize_cRotate
#print axioms cRotate_gap121
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RootCommonFactorPlusWord

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RootCommonFactorPlusScalar
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144Nat
open RootCommonFactorPlusProduct
open Paired80Product (factor)

private theorem coefficient_nat : coefficient.toNat = (2^32+1)*(2+2^65) := by decide
private theorem factor_nat : factor.toNat = 2^32+1 := by decide

private theorem low_shift_nat (x : BitVec 256) (n : Nat) :
    (low (x >>> n)).toNat = x.toNat / 2^n % 2^32 := by
  simp only [low, BitVec.extractLsb'_toNat, Nat.pow_zero, Nat.div_one,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem low_product_nat (x c : BitVec 256) (value n : Nat) (hc : c.toNat=value) :
    (low ((x*c) >>> n)).toNat = (x.toNat*value%2^256)/2^n%2^32 :=
  (low_shift_nat (x*c) n).trans
    (congrArg (fun z : Nat => z/2^n%2^32)
      ((BitVec.toNat_mul x c).trans
        (congrArg (fun z : Nat => x.toNat*z%2^256) hc)))

theorem scalar_window (x n : Nat) (hn0 : 1 ≤ n) (hn : n ≤ 33) :
    (x*((2^32+1)*(2+2^65))%2^256)/2^n%2^32 =
      (x*(2^32+1)%2^256)/2^(n-1)%2^32 := by
  rw [truncate_window _ n 32 256 (by omega),
    truncate_window _ (n-1) 32 256 (by omega),
    ← Nat.mul_assoc, Nat.mul_add,
    div_pow_add_mul_pow _ _ n 65 (by omega),
    mod_pow_add_mul_pow _ _ (65-n) 32 (by omega)]
  exact congrArg (fun k : Nat => k % 2^32) (mul_pow_div_pow (x*(2^32+1)) 1 n hn0)

theorem low_window (x : BitVec 256) (n : Nat) (hn0 : 1 ≤ n) (hn : n ≤ 33) :
    low ((x * coefficient) >>> n) = low ((x * factor) >>> (n-1)) := by
  apply BitVec.eq_of_toNat_eq
  exact (low_product_nat x coefficient _ n coefficient_nat).trans
    ((scalar_window x.toNat n hn0 hn).trans
      (low_product_nat x factor _ (n-1) factor_nat).symm)

theorem product_window (a b n : Nat) (hn0 : 1 ≤ n) (hn : n ≤ 33) :
    (((a + b * 2^144) * ((2^32+1)*(2+2^65))) % 2^256) / 2^n % 2^32 =
      a * (2^32+1) / 2^(n-1) % 2^32 := by
  rw [truncate_window _ n 32 256 (by omega)]
  have hd : (a + b * 2^144) * ((2^32+1)*(2+2^65)) =
      a * ((2^32+1)*(2+2^65)) + (b * ((2^32+1)*(2+2^65))) * 2^144 := by
    rw [Nat.add_mul]
    ac_rfl
  rw [hd, div_pow_add_mul_pow _ _ n 144 (by omega),
    mod_pow_add_mul_pow _ _ (144-n) 32 (by omega),
    ← Nat.mul_assoc, Nat.mul_add,
    div_pow_add_mul_pow _ _ n 65 (by omega),
    mod_pow_add_mul_pow _ _ (65-n) 32 (by omega)]
  exact congrArg (fun k : Nat => k % 2^32) (mul_pow_div_pow (a*(2^32+1)) 1 n hn0)

theorem low_pack_rotate (a b : BitVec 32) (r : Nat) (hr0 : 0 < r) (hr : r < 32) :
    low ((pack a b * coefficient) >>> (33-r)) = a.rotateLeft r := by
  apply BitVec.eq_of_toNat_eq
  rw [low_product_nat _ _ _ _ coefficient_nat, pack_toNat,
    product_window _ _ (33-r) (by omega) (by omega),
    show 33-r-1 = 32-r by omega]
  exact (rotate_toNat a r hr0 hr).symm

theorem wide_low_eq (x : BitVec 256) :
    low ((x * coefficient) >>> 23) = low ((x * factor) >>> 22) :=
  low_window x 23 (by decide) (by decide)

theorem low54_product_shift_eq (x y : BitVec 256)
    (h : x.setWidth 54 = y.setWidth 54) :
    low ((x * factor) >>> 22) = low ((y * factor) >>> 22) := by
  have hp : (x * factor).setWidth 54 = (y * factor).setWidth 54 := by
    rw [BitVec.setWidth_mul _ _ (by decide), BitVec.setWidth_mul _ _ (by decide), h]
  have hh := congrArg (fun z : BitVec 54 => z.extractLsb' 22 32) hp
  rw [BitVec.extractLsb'_setWidth_of_le (by decide),
    BitVec.extractLsb'_setWidth_of_le (by decide)] at hh
  change ((x * factor) >>> 22).setWidth 32 = ((y * factor) >>> 22).setWidth 32
  simpa only [BitVec.setWidth_ushiftRight_eq_extractLsb] using hh

theorem low_rotate_low54 (x : BitVec 256)
    (hx : x.setWidth 54 = (pack (low x) 0#32).setWidth 54) :
    low ((x * coefficient) >>> 23) = (low x).rotateLeft 10 := by
  rw [wide_low_eq, low54_product_shift_eq x (pack (low x) 0#32) hx,
    ← wide_low_eq (pack (low x) 0#32)]
  exact low_pack_rotate (low x) 0#32 10 (by decide) (by decide)

theorem low_word_rotate_low54 (c : UInt256)
    (hc : (bits c).setWidth 54 = (pack (low (bits c)) 0#32).setWidth 54) :
    low (bits (RootCommonFactorPlusWord.wordShift c 23)) = (low (bits c)).rotateLeft 10 := by
  rw [RootCommonFactorPlusWord.bits_wordShift _ 23 (by decide)]
  exact low_rotate_low54 _ hc

#print axioms scalar_window
#print axioms low_window
#print axioms product_window
#print axioms low_pack_rotate
#print axioms wide_low_eq
#print axioms low_rotate_low54
#print axioms low_word_rotate_low54
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RootCommonFactorPlusScalar
