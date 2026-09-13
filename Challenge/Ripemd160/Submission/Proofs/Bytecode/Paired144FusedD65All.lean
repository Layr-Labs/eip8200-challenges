import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CompactRotation
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace RootFusedD65All

open Challenge.Ripemd160.Submission.Proofs.Bytecode
open Paired144Core

def d : Nat := 2 ^ 65
def base : Nat := 2 ^ 144
def c : Nat := 2 ^ 32 + 1
def km (k : Nat) : Nat := c * (1 + d * (2 ^ k - 1))
def kp (k : Nat) : Nat := c * (2 ^ k + d * (2 ^ k - 1))
def coefficient (positive : Bool) (k : Nat) : Nat := if positive then kp k else km k
def modulus (positive : Bool) : Nat := (if positive then d + 1 else d - 1) * base
def loScale (positive : Bool) (k : Nat) : Nat := if positive then k else 0
def hiScale (positive : Bool) (k : Nat) : Nat := if positive then 0 else k
def highPart (positive : Bool) (b k : Nat) : Nat :=
  if positive then b * c else (b * c * 2 ^ k) % (d - 1)
def canonical (positive : Bool) (a b k : Nat) : Nat :=
  a * coefficient positive k + highPart positive b k * base

theorem lowPart_bound (positive : Bool) (a k : Nat) (ha : a < 2 ^ 32)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 10) : a * coefficient positive k < 2 ^ 143 := by
  have hc : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
  rcases hc with h | h | h | h | h | h | h | h | h | h <;> subst k <;> cases positive <;>
    simp only [coefficient, kp, km, c, d, if_true, if_false, Bool.false_eq_true,
      Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul] at * <;> omega

theorem highPart_bound (positive : Bool) (b k : Nat) (hb : b < 2 ^ 32) :
    highPart positive b k < d := by
  cases positive with
  | false =>
      have h := Nat.mod_lt (b * c * 2 ^ k) (by decide : 0 < d - 1)
      simpa only [highPart, if_false, Bool.false_eq_true] using Nat.lt_trans h (by decide : d - 1 < d)
  | true => simp only [highPart, if_true, c, d, Nat.reducePow, Nat.reduceAdd] at *; omega

theorem canonical_bound (positive : Bool) (a b k : Nat)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hk0 : 1 ≤ k) (hk1 : k ≤ 10) :
    canonical positive a b k < 2 ^ 256 := by
  have hl := lowPart_bound positive a k ha hk0 hk1
  have hh := highPart_bound positive b k hb
  simp only [canonical, base, d, Nat.reducePow] at *
  omega

theorem minus_residue (a b k : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 10) :
    ((a + b * base) * km k) % ((d - 1) * base) = canonical false a b k := by
  have hdiv := Nat.mod_add_div (b * c * 2 ^ k) (d - 1)
  have hl := lowPart_bound false a k ha hk0 hk1
  have hr := Nat.mod_lt (b * c * 2 ^ k) (by decide : 0 < d - 1)
  have hsplit : (a + b * base) * km k = canonical false a b k +
      (b * c * (2 ^ k - 1) + b * c * 2 ^ k / (d - 1)) * ((d - 1) * base) := by
    have hc : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
    rcases hc with h | h | h | h | h | h | h | h | h | h <;> subst k <;>
      simp only [canonical, coefficient, highPart, km, base, d, c, if_false, Bool.false_eq_true,
        Nat.add_mul, Nat.mul_assoc, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul] at * <;> omega
  have hlt : canonical false a b k < (d - 1) * base := by
    simp only [canonical, coefficient, highPart, if_false, Bool.false_eq_true, base, d, Nat.reducePow,
      Nat.reduceSub, Nat.reduceMul] at *
    omega
  rw [hsplit, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

theorem plus_residue (a b k : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 10) :
    ((a + b * base) * kp k) % ((d + 1) * base) = canonical true a b k := by
  have hl := lowPart_bound true a k ha hk0 hk1
  have hsplit : (a + b * base) * kp k = canonical true a b k +
      (b * c * (2 ^ k - 1)) * ((d + 1) * base) := by
    have hc : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
    rcases hc with h | h | h | h | h | h | h | h | h | h <;> subst k <;>
      simp only [canonical, coefficient, highPart, kp, base, d, c, if_true,
        Nat.add_mul, Nat.mul_assoc, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul] <;> omega
  have hlt : canonical true a b k < (d + 1) * base := by
    simp only [canonical, coefficient, highPart, if_true, base, d, c, Nat.reducePow,
      Nat.reduceAdd, Nat.reduceMul] at *
    omega
  rw [hsplit, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]

theorem canonical_residue (positive : Bool) (a b k : Nat)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hk0 : 1 ≤ k) (hk1 : k ≤ 10) :
    ((a + b * base) * coefficient positive k) % modulus positive = canonical positive a b k := by
  cases positive
  · exact minus_residue a b k ha hb hk0 hk1
  · exact plus_residue a b k ha hb hk0 hk1

theorem canonical_low (positive : Bool) (a b k : Nat) :
    canonical positive a b k % d = (a * c * 2 ^ loScale positive k) % d := by
  have hsplit : canonical positive a b k = a * c * 2 ^ loScale positive k +
      (a * c * (2 ^ k - 1) + highPart positive b k * 2 ^ 79) * d := by
    cases positive <;> simp only [canonical, coefficient, loScale, if_true, if_false,
      Bool.false_eq_true, km, kp, base, d, c, Nat.pow_zero, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.mul_one] <;> omega
  rw [hsplit, Nat.add_mul_mod_self_right]

theorem canonical_high (positive : Bool) (a b k : Nat)
    (ha : a < 2 ^ 32) (hk0 : 1 ≤ k) (hk1 : k ≤ 10) :
    canonical positive a b k / base = highPart positive b k := by
  have hl : a * coefficient positive k < base :=
    Nat.lt_trans (lowPart_bound positive a k ha hk0 hk1) (by decide : 2 ^ 143 < base)
  rw [canonical, Nat.add_mul_div_right _ _ (by decide : 0 < base), Nat.div_eq_of_lt hl, Nat.zero_add]

theorem canonical_gap (positive : Bool) (a b k : Nat)
    (ha : a < 2 ^ 32) (hk0 : 1 ≤ k) (hk1 : k ≤ 10) :
    canonical positive a b k % base < 2 ^ 143 := by
  have hl := lowPart_bound positive a k ha hk0 hk1
  rw [canonical, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Nat.lt_trans hl (by decide : 2 ^ 143 < base))]
  exact hl

theorem quotient_small (b k : Nat) (hb : b < 2 ^ 32) : b * c * 2 ^ k / (d - 1) < 2 ^ k := by
  have hbc : b * c < d - 1 := by simp only [c, d, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub] at *; omega
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < d - 1)).2
  simpa only [Nat.mul_comm (2 ^ k)] using Nat.mul_lt_mul_of_pos_right hbc (Nat.two_pow_pos k)

theorem mod_minus_window (D A k n w : Nat) (hD : 1 ≤ D)
    (hq : A * 2 ^ k / (D - 1) < 2 ^ k)
    (hd : 2 ^ (n + w) ∣ D) (hkn : k ≤ n) :
    (A * 2 ^ k % (D - 1)) / 2 ^ n % 2 ^ w = A * 2 ^ k / 2 ^ n % 2 ^ w := by
  let H := A * 2 ^ k
  let q := H / (D - 1)
  have hrel : H % (D - 1) + q * D = H + q := by
    have hD1 : D = (D - 1) + 1 := (Nat.sub_add_cancel hD).symm
    have hsplit : q * D = q * (D - 1) + q := by
      calc
        q * D = q * ((D - 1) + 1) := congrArg (fun z => q * z) hD1
        _ = q * (D - 1) + q := by rw [Nat.mul_add, Nat.mul_one]
    rw [hsplit, ← Nat.add_assoc, Nat.mul_comm q (D - 1)]
    exact congrArg (fun z => z + q) (Nat.mod_add_div H (D - 1))
  have hmod : (H % (D - 1)) % 2 ^ (n + w) = (H + q) % 2 ^ (n + w) := by
    have hqd : (q * D) % 2 ^ (n + w) = 0 := by
      rw [Nat.mul_mod q D _, Nat.mod_eq_zero_of_dvd hd, Nat.mul_zero, Nat.zero_mod]
    rw [← hrel, Nat.add_mod, hqd]
    simp only [Nat.add_zero, Nat.mod_mod]
  have hdivq : (H + q) / 2 ^ k = A := by
    dsimp [H]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hq, Nat.zero_add]
  have hdivh : H / 2 ^ k = A := by dsimp [H]; exact Nat.mul_div_cancel _ (Nat.two_pow_pos k)
  have hpow : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← Nat.pow_add, Nat.add_sub_of_le hkn]
  have hsame : (H + q) / 2 ^ n = H / 2 ^ n := by
    rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdivq, hdivh]
  change (H % (D - 1)) / 2 ^ n % 2 ^ w = H / 2 ^ n % 2 ^ w
  rw [← Paired144Nat.truncate_window _ n w (n + w) (Nat.le_refl _), hmod,
    Paired144Nat.truncate_window _ n w (n + w) (Nat.le_refl _), hsame]

theorem highPart_window (positive : Bool) (b k n : Nat) (hb : b < 2 ^ 32)
    (hkn : k ≤ n) (hn : n + 32 ≤ 65) :
    highPart positive b k / 2 ^ n % 2 ^ 32 = b * c * 2 ^ hiScale positive k / 2 ^ n % 2 ^ 32 := by
  cases positive with
  | true => simp only [highPart, hiScale, if_true, Nat.pow_zero, Nat.mul_one]
  | false =>
      simp only [highPart, hiScale, if_false, Bool.false_eq_true]
      exact mod_minus_window d (b * c) k n 32 (by decide) (quotient_small b k hb)
        (Nat.pow_dvd_pow 2 hn) hkn

def rawProduct (positive : Bool) (a b : BitVec 32) (k : Nat) : BitVec 256 :=
  BitVec.ofNat 256 (canonical positive a.toNat b.toNat k)

theorem raw_toNat (positive : Bool) (a b : BitVec 32) (k : Nat)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 10) :
    (rawProduct positive a b k).toNat = canonical positive a.toNat b.toNat k := by
  rw [rawProduct, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (canonical_bound positive a.toNat b.toNat k a.isLt b.isLt hk0 hk1)]

theorem raw_low65 (positive : Bool) (a b : BitVec 32) (k : Nat)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 10) :
    (rawProduct positive a b k).toNat % 2 ^ 65 =
      (a.toNat * c * 2 ^ loScale positive k) % 2 ^ 65 := by
  rw [raw_toNat positive a b k hk0 hk1]
  exact canonical_low positive a.toNat b.toNat k

theorem raw_high144 (positive : Bool) (a b : BitVec 32) (k : Nat)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 10) :
    (rawProduct positive a b k).toNat / 2 ^ 144 = highPart positive b.toNat k := by
  rw [raw_toNat positive a b k hk0 hk1]
  exact canonical_high positive a.toNat b.toNat k a.isLt hk0 hk1

theorem raw_gap143 (positive : Bool) (a b : BitVec 32) (k : Nat)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 10) :
    (rawProduct positive a b k).getLsbD 143 = false := by
  have hlow : (rawProduct positive a b k).toNat % 2 ^ 144 < 2 ^ 143 := by
    rw [raw_toNat positive a b k hk0 hk1]
    exact canonical_gap positive a.toNat b.toNat k a.isLt hk0 hk1
  rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  apply decide_eq_false_iff_not.mpr
  simp only [Nat.reducePow] at *
  omega

private theorem scaled_rotate_nat (a : BitVec 32) (u n : Nat)
    (hun : u < n) (hn : n < 32) :
    a.toNat * c * 2 ^ u / 2 ^ n % 2 ^ 32 =
      (a.rotateLeft (32 + u - n)).toNat := by
  have hr0 : 0 < 32 + u - n := by omega
  have hr : 32 + u - n < 32 := by omega
  have he : n - u = 32 - (32 + u - n) := by omega
  rw [Paired144Nat.rotate_toNat a _ hr0 hr,
    Paired144Nat.mul_pow_div_pow _ _ _ (by omega), he]
  rfl

theorem low_shifted_of_mod (x : BitVec 256) (a : BitVec 32) (u n : Nat)
    (he : x.toNat % 2 ^ 65 = (a.toNat * c * 2 ^ u) % 2 ^ 65)
    (hun : u < n) (hn : n < 32) (hn65 : n + 32 ≤ 65) :
    low (x >>> n) = a.rotateLeft (32 + u - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [low, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  rw [← Paired144Nat.truncate_window _ n 32 65 hn65, he,
    Paired144Nat.truncate_window _ n 32 65 hn65]
  exact scaled_rotate_nat a u n hun hn

theorem high_shifted_of_window (x : BitVec 256) (b : BitVec 32) (v n : Nat)
    (he : x.toNat / 2 ^ 144 / 2 ^ n % 2 ^ 32 = b.toNat * c * 2 ^ v / 2 ^ n % 2 ^ 32)
    (hvn : v < n) (hn : n < 32) :
    high (x >>> n) = b.rotateLeft (32 + v - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [high, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ n) (2 ^ 144),
    ← Nat.div_div_eq_div_mul, he]
  exact scaled_rotate_nat b v n hvn hn

theorem low_shifted (positive : Bool) (a b : BitVec 32) (k n : Nat)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 10) (hn0 : 11 ≤ n) (hn1 : n ≤ 31) :
    low (rawProduct positive a b k >>> n) = a.rotateLeft (32 + loScale positive k - n) := by
  have hu : loScale positive k ≤ 10 := by cases positive <;> simp [loScale] <;> omega
  exact low_shifted_of_mod (rawProduct positive a b k) a (loScale positive k) n
    (raw_low65 positive a b k hk0 hk1) (by omega) (by omega) (by omega)

theorem high_shifted (positive : Bool) (a b : BitVec 32) (k n : Nat)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 10) (hn0 : 11 ≤ n) (hn1 : n ≤ 31) :
    high (rawProduct positive a b k >>> n) = b.rotateLeft (32 + hiScale positive k - n) := by
  have hv : hiScale positive k ≤ 10 := by cases positive <;> simp [hiScale] <;> omega
  apply high_shifted_of_window (rawProduct positive a b k) b (hiScale positive k) n
    ?_ (by omega) (by omega)
  rw [raw_high144 positive a b k hk0 hk1]
  exact highPart_window positive b.toNat k n b.isLt (by omega) (by omega)

theorem normalize_shifted_add (positive : Bool) (a b e f : BitVec 32) (k n : Nat)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 10) (hn0 : 11 ≤ n) (hn1 : n ≤ 31) :
    normalize ((rawProduct positive a b k >>> n) + pack e f) =
      pack (a.rotateLeft (32 + loScale positive k - n) + e)
        (b.rotateLeft (32 + hiScale positive k - n) + f) := by
  have hgap : (rawProduct positive a b k >>> n).getLsbD (143 - n) = false := by
    rw [BitVec.getLsbD_ushiftRight]
    have he : n + (143 - n) = 143 := by omega
    rw [he]
    exact raw_gap143 positive a b k hk0 hk1
  rw [Paired144Carry.normalize_add_pack _ e f (143 - n) (by omega) (by omega) hgap,
    low_shifted positive a b k n hk0 hk1 hn0 hn1,
    high_shifted positive a b k n hk0 hk1 hn0 hn1]


open EvmSemantics PairedLaneUInt256Bridge

def fusedCoefficientWord (u v : Nat) : UInt256 :=
  UInt256.ofNat ((2 ^ 32 + 1) * (2 ^ u + 2 ^ 65 *
    (if u < v then 2 ^ v - 2 ^ u else 2 ^ u - 2 ^ v)))
def fusedModulusWord (r s : Nat) : UInt256 :=
  UInt256.ofNat ((if r < s then 2 ^ 65 - 1 else 2 ^ 65 + 1) * 2 ^ 144)
def wordFusedRotate (x : UInt256) (r s : Nat) : UInt256 :=
  UInt256.shiftRight
    (UInt256.mulMod (UInt256.land x Paired144WordRound.pairWord)
      (fusedCoefficientWord (r - s) (s - r)) (fusedModulusWord r s))
    (UInt256.ofNat (32 - min r s))

theorem uint256_ofNat_toNat_small (v : Nat) (hv : v < 2 ^ 256) :
    (UInt256.ofNat v).toNat = v := by
  change v % (2 ^ 256) = v
  exact Nat.mod_eq_of_lt hv

theorem bits_mulMod_ofNat (x : UInt256) (K N : Nat)
    (hK : K < 2 ^ 256) (hN : N < 2 ^ 256) (hN0 : N ≠ 0) :
    bits (UInt256.mulMod x (UInt256.ofNat K) (UInt256.ofNat N)) =
      BitVec.ofNat 256 (x.toNat * K % N) := by
  have hKv := uint256_ofNat_toNat_small K hK
  have hNv := uint256_ofNat_toNat_small N hN
  unfold UInt256.mulMod
  change bits (if (UInt256.ofNat N).toNat = 0 then ⟨0⟩ else
    UInt256.ofNat ((x.toNat * (UInt256.ofNat K).toNat) % (UInt256.ofNat N).toNat)) = _
  rw [hNv, if_neg hN0, hKv, bits_ofNat]

theorem modulus_small (positive : Bool) : modulus positive < 2 ^ 256 := by
  cases positive <;> decide

theorem modulus_ne_zero (positive : Bool) : modulus positive ≠ 0 := by
  cases positive <;> decide

theorem coefficient_small (positive : Bool) (k : Nat) (hk0 : 1 ≤ k) (hk1 : k ≤ 10) :
    coefficient positive k < 2 ^ 256 := by
  have h := lowPart_bound positive 1 k (by decide) hk0 hk1
  rw [Nat.one_mul] at h
  exact Nat.lt_trans h (by decide)

theorem masked_input (x : UInt256) (a b : BitVec 32)
    (hx : normalize (bits x) = pack a b) :
    (UInt256.land x Paired144WordRound.pairWord).toNat = a.toNat + b.toNat * base := by
  rw [← bits_toNat, bits_land, Paired144WordRound.pairWord, bits_word,
    ← normalize_eq_and, hx, pack_toNat]
  rfl

theorem bits_fused_product (x : UInt256) (a b : BitVec 32) (positive : Bool) (k : Nat)
    (hx : normalize (bits x) = pack a b) (hk0 : 1 ≤ k) (hk1 : k ≤ 10) :
    bits (UInt256.mulMod (UInt256.land x Paired144WordRound.pairWord)
      (UInt256.ofNat (coefficient positive k)) (UInt256.ofNat (modulus positive))) =
      rawProduct positive a b k := by
  rw [bits_mulMod_ofNat _ _ _ (coefficient_small positive k hk0 hk1)
    (modulus_small positive) (modulus_ne_zero positive), masked_input x a b hx,
    canonical_residue positive a.toNat b.toNat k a.isLt b.isLt hk0 hk1]
  rfl

theorem normalize_fused_product_add (x : UInt256) (a b e f : BitVec 32)
    (positive : Bool) (k n : Nat) (hx : normalize (bits x) = pack a b)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 10) (hn0 : 11 ≤ n) (hn1 : n ≤ 31) :
    normalize (bits (UInt256.shiftRight
      (UInt256.mulMod (UInt256.land x Paired144WordRound.pairWord)
        (UInt256.ofNat (coefficient positive k)) (UInt256.ofNat (modulus positive)))
      (UInt256.ofNat n)) + pack e f) =
      pack (a.rotateLeft (32 + loScale positive k - n) + e)
        (b.rotateLeft (32 + hiScale positive k - n) + f) := by
  rw [bits_shr _ n (by omega), bits_fused_product x a b positive k hx hk0 hk1]
  exact normalize_shifted_add positive a b e f k n hk0 hk1 hn0 hn1


theorem normalize_wordFusedRotate_add_all (x : UInt256) (a b e f : BitVec 32) (r s : Nat)
    (hx : normalize (bits x) = pack a b)
    (hr0 : 5 ≤ r) (hr1 : r ≤ 15) (hs0 : 5 ≤ s) (hs1 : s ≤ 15)
    (hne : r ≠ s) :
    normalize (bits (wordFusedRotate x r s) + pack e f) =
      pack (a.rotateLeft r + e) (b.rotateLeft s + f) := by
  have hb : (r < s ∧ s - r ≤ 10) ∨ (s < r ∧ r - s ≤ 10) := by omega
  rcases hb with ⟨hrs, hk⟩ | ⟨hsr, hk⟩
  · have hzero : r - s = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hrs)
    have hpos : 0 < s - r := Nat.sub_pos_of_lt hrs
    have hcoeff : fusedCoefficientWord (r - s) (s - r) =
        UInt256.ofNat (coefficient false (s - r)) := by
      simp only [fusedCoefficientWord, hzero, Nat.pow_zero, if_pos hpos,
        coefficient, Bool.false_eq_true, if_false, km, c, d]
    have hmod : fusedModulusWord r s = UInt256.ofNat (modulus false) := by
      simp only [fusedModulusWord, if_pos hrs, modulus, Bool.false_eq_true, if_false, d, base]
    unfold wordFusedRotate
    rw [hcoeff, hmod, Nat.min_eq_left (Nat.le_of_lt hrs)]
    have h := normalize_fused_product_add x a b e f false (s - r) (32 - r) hx
      (by omega) hk (by omega) (by omega)
    have hl : 32 + loScale false (s - r) - (32 - r) = r := by simp only [loScale, Bool.false_eq_true, if_false]; omega
    have hh : 32 + hiScale false (s - r) - (32 - r) = s := by simp only [hiScale, Bool.false_eq_true, if_false]; omega
    simpa only [hl, hh] using h
  · have hzero : s - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hsr)
    have hnrs : ¬ r < s := by omega
    have hcoeff : fusedCoefficientWord (r - s) (s - r) =
        UInt256.ofNat (coefficient true (r - s)) := by
      simp only [fusedCoefficientWord, hzero, Nat.pow_zero, Nat.not_lt_zero, if_false,
        coefficient, if_true, kp, c, d]
    have hmod : fusedModulusWord r s = UInt256.ofNat (modulus true) := by
      simp only [fusedModulusWord, if_neg hnrs, modulus, if_true, d, base]
    unfold wordFusedRotate
    rw [hcoeff, hmod, Nat.min_eq_right (Nat.le_of_lt hsr)]
    have h := normalize_fused_product_add x a b e f true (r - s) (32 - s) hx
      (by omega) hk (by omega) (by omega)
    have hl : 32 + loScale true (r - s) - (32 - s) = r := by simp only [loScale, if_true]; omega
    have hh : 32 + hiScale true (r - s) - (32 - s) = s := by simp only [hiScale, if_true]; omega
    simpa only [hl, hh] using h

#print axioms bits_fused_product
#print axioms normalize_fused_product_add
#print axioms normalize_wordFusedRotate_add_all
end RootFusedD65All

namespace RootFusedD65All
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open EvmSemantics PairedLaneUInt256Bridge
open Paired144Core

/-- Nine distinct pairs at the ten newly targeted executed rotation sites. -/
def extensionPair (r s : Nat) : Prop :=
  (r = 15 ∧ s = 5) ∨ (r = 15 ∧ s = 6) ∨ (r = 6 ∧ s = 15) ∨
  (r = 14 ∧ s = 13) ∨ (r = 8 ∧ s = 7) ∨ (r = 9 ∧ s = 8) ∨
  (r = 13 ∧ s = 14) ∨ (r = 7 ∧ s = 6) ∨ (r = 6 ∧ s = 7)

theorem extensionPair_bounds (r s : Nat) (h : extensionPair r s) :
    5 ≤ r ∧ r ≤ 15 ∧ 5 ≤ s ∧ s ≤ 15 ∧ r ≠ s := by
  rcases h with h | h | h | h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;> decide

theorem current_wordFusedRotate_add_all (x : UInt256) (a b e f : BitVec 32) (r s : Nat)
    (hx : normalize (bits x) = pack a b)
    (hr0 : 5 ≤ r) (hr1 : r ≤ 15) (hs0 : 5 ≤ s) (hs1 : s ≤ 15) (hne : r ≠ s) :
    normalize (bits (Paired144WordRound.wordFusedRotate x r s) + pack e f) =
      pack (a.rotateLeft r + e) (b.rotateLeft s + f) := by
  simpa only [Paired144WordRound.wordFusedRotate, Paired144WordRound.fusedCoefficientWord,
    Paired144WordRound.fusedModulusWord, wordFusedRotate, fusedCoefficientWord, fusedModulusWord]
    using normalize_wordFusedRotate_add_all x a b e f r s hx hr0 hr1 hs0 hs1 hne

theorem current_wordFusedRotate_add_extension (x : UInt256) (a b e f : BitVec 32) (r s : Nat)
    (hx : normalize (bits x) = pack a b) (h : extensionPair r s) :
    normalize (bits (Paired144WordRound.wordFusedRotate x r s) + pack e f) =
      pack (a.rotateLeft r + e) (b.rotateLeft s + f) := by
  obtain ⟨hr0,hr1,hs0,hs1,hne⟩ := extensionPair_bounds r s h
  exact current_wordFusedRotate_add_all x a b e f r s hx hr0 hr1 hs0 hs1 hne

#print axioms current_wordFusedRotate_add_all
#print axioms current_wordFusedRotate_add_extension
end RootFusedD65All
