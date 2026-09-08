import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P7
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P8
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P9
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P10
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P11
import Challenge.Modexp.Submission.Proofs.Fast.Csub
import Challenge.Modexp.Submission.Proofs.Bytecode.LoopPCs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# The `MONPRO` subroutine of the appended Montgomery path

`MONPRO` occupies instruction indices 1379..1599 (pc 1939..2466).  It is
entered with stack `[pa, pb, pc, ret]`, computes the CIOS Montgomery product
`a * b * R⁻¹ mod m` of the `n`-limb blocks at `pa` and `pb` into the CIOS
scratch area, and tail-calls `CSUB` at pc 2642 with stack `[pc, ret]`.

This module starts with the 512-bit multiply-accumulate identity that every
CIOS row step relies on.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Monpro

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

/-! ## Word arithmetic -/

theorem word_toNat_mul (a b : UInt256) :
    (a * b).toNat = a.toNat * b.toNat % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

theorem word_toNat_lt' (a b : UInt256) :
    (UInt256.lt a b).toNat = if a.toNat < b.toNat then 1 else 0 :=
  Challenge.EvmProof.Word.word_toNat_lt a b

theorem word_lt_size (a : UInt256) : a.toNat < 2 ^ 256 := a.val.isLt

/-- The `PUSH32` immediate the 512-bit multiply uses as the `MULMOD` modulus. -/
def maxWord : UInt256 :=
  UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935

theorem maxWord_toNat : maxWord.toNat = 2 ^ 256 - 1 := by
  rw [maxWord, Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num

theorem word_toNat_mulMod_max (a b : UInt256) :
    (UInt256.mulMod a b maxWord).toNat = a.toNat * b.toNat % (2 ^ 256 - 1) := by
  have hne : maxWord.val.val ≠ 0 := by
    have : maxWord.toNat = 2 ^ 256 - 1 := maxWord_toNat
    change maxWord.toNat ≠ 0
    omega
  rw [UInt256.mulMod, if_neg hne, Challenge.EvmProof.Word.word_toNat_ofNat,
    maxWord_toNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le
    (Nat.mod_lt _ (by norm_num)) (by norm_num))

/-! ## The 512-bit product

`lo = mul x y`, `mm = mulmod x y (2^256-1)`, `hi = mm - (lo + lt mm lo)`
satisfies `hi * 2^256 + lo = x * y` over the naturals. -/

/-- The high word of the 512-bit product, exactly as the bytecode computes it. -/
def mulHi (x y : UInt256) : UInt256 :=
  UInt256.mulMod x y maxWord - (x * y + UInt256.lt (UInt256.mulMod x y maxWord) (x * y))

theorem high_lt {K X Y : Nat} (hK : 2 ≤ K) (hX : X < K) (hY : Y < K) :
    X * Y / K < K - 1 := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 2 := ⟨K - 2, by omega⟩
  rw [Nat.div_lt_iff_lt_mul (by omega), show K' + 2 - 1 = K' + 1 from by omega]
  have h1 : X * Y ≤ (K' + 1) * (K' + 1) := Nat.mul_le_mul (by omega) (by omega)
  nlinarith

private theorem mulHi_core {K H L M : Nat} (hK : 2 ≤ K)
    (hH : H + 1 < K) (hL : L < K) (hM : M = (H + L) % (K - 1)) :
    (K + M - (L + (if M < L then 1 else 0)) % K) % K = H := by
  rcases Nat.lt_or_ge (H + L) (K - 1) with hcase | hcase
  · have hMv : M = H + L := by rw [hM]; exact Nat.mod_eq_of_lt hcase
    rw [if_neg (by omega), Nat.add_zero, Nat.mod_eq_of_lt hL,
      show K + M - L = H + K by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · have hMv : M = H + L - (K - 1) := by
      rw [hM, Nat.mod_eq_sub_mod hcase, Nat.mod_eq_of_lt (by omega)]
    rw [if_pos (by omega)]
    rcases Nat.lt_or_ge (L + 1) K with hsub | hsub
    · rw [Nat.mod_eq_of_lt hsub, show K + M - (L + 1) = H by omega,
        Nat.mod_eq_of_lt (by omega)]
    · have hLK : L + 1 = K := by omega
      rw [hLK, Nat.mod_self, Nat.sub_zero, Nat.add_mod_left,
        Nat.mod_eq_of_lt (show M < K by omega)]
      omega

theorem mulHi_toNat (x y : UInt256) :
    (mulHi x y).toNat = x.toNat * y.toNat / 2 ^ 256 := by
  have hXlt : x.toNat < 2 ^ 256 := word_lt_size x
  have hYlt : y.toNat < 2 ^ 256 := word_lt_size y
  have hHlt : x.toNat * y.toNat / 2 ^ 256 < 2 ^ 256 - 1 :=
    high_lt (by norm_num) hXlt hYlt
  have hdm : 2 ^ 256 * (x.toNat * y.toNat / 2 ^ 256) + x.toNat * y.toNat % 2 ^ 256
      = x.toNat * y.toNat := Nat.div_add_mod _ _
  have hmodeq : (2 : Nat) ^ 256 ≡ 1 [MOD 2 ^ 256 - 1] := by
    unfold Nat.ModEq
    norm_num
  have hstep := (hmodeq.mul_right (x.toNat * y.toNat / 2 ^ 256)).add_right
    (x.toNat * y.toNat % 2 ^ 256)
  rw [Nat.one_mul, hdm] at hstep
  rw [mulHi, Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_add, word_toNat_mulMod_max,
    word_toNat_mul, word_toNat_lt', word_toNat_mulMod_max, word_toNat_mul]
  exact mulHi_core (K := 2 ^ 256) (by norm_num) (by omega)
    (Nat.mod_lt _ (by norm_num)) hstep

/-- The 512-bit product identity. -/
theorem mulHi_spec (x y : UInt256) :
    (mulHi x y).toNat * 2 ^ 256 + (x * y).toNat = x.toNat * y.toNat := by
  rw [mulHi_toNat, word_toNat_mul, Nat.mul_comm]
  exact Nat.div_add_mod _ _

/-! ## The multiply-accumulate step

Both CIOS limb loops execute the same instruction sequence: read the source
limb `x`, form the 512-bit product with the row multiplier `y`, add the
current `t` limb and the running carry, store the low word back and keep the
high word as the new carry. -/

/-- The stored limb of one multiply-accumulate step. -/
def macSum (x y t c : UInt256) : UInt256 := c + (t + x * y)

/-- The carry out of one multiply-accumulate step. -/
def macCarry (x y t c : UInt256) : UInt256 :=
  UInt256.lt (c + (t + x * y)) c + (UInt256.lt (t + x * y) t + mulHi x y)

theorem carry_split (A B : Nat) (hA : A < 2 ^ 256) (hB : B < 2 ^ 256) :
    A + B = (if (A + B) % 2 ^ 256 < A then 1 else 0) * 2 ^ 256 + (A + B) % 2 ^ 256 := by
  rcases Nat.lt_or_ge (A + B) (2 ^ 256) with h | h
  · rw [Nat.mod_eq_of_lt h, if_neg (by omega)]
    omega
  · have hval : (A + B) % 2 ^ 256 = A + B - 2 ^ 256 := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [hval, if_pos (by omega)]
    omega

private theorem total_lt {K T X Y C : Nat} (hT : T < K) (hX : X < K) (hY : Y < K)
    (hC : C < K) : T + X * Y + C < K * K := by
  have h : X * Y ≤ (K - 1) * (K - 1) := Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  nlinarith

/-- One multiply-accumulate step is exact over the naturals. -/
theorem macSpec (x y t c : UInt256) :
    (macCarry x y t c).toNat * 2 ^ 256 + (macSum x y t c).toNat =
      t.toNat + x.toNat * y.toNat + c.toNat := by
  have hx : x.toNat < 2 ^ 256 := word_lt_size x
  have hy : y.toNat < 2 ^ 256 := word_lt_size y
  have ht : t.toNat < 2 ^ 256 := word_lt_size t
  have hc : c.toNat < 2 ^ 256 := word_lt_size c
  have hprod := mulHi_spec x y
  have hlo : (x * y).toNat < 2 ^ 256 := word_lt_size (x * y)
  have hs1lt : (t + x * y).toNat < 2 ^ 256 := word_lt_size (t + x * y)
  have h1 : t.toNat + (x * y).toNat =
      (UInt256.lt (t + x * y) t).toNat * 2 ^ 256 + (t + x * y).toNat := by
    rw [word_toNat_lt', Challenge.EvmProof.Word.word_toNat_add t (x * y)]
    exact carry_split t.toNat (x * y).toNat ht hlo
  have h2 : c.toNat + (t + x * y).toNat =
      (UInt256.lt (c + (t + x * y)) c).toNat * 2 ^ 256 +
        (c + (t + x * y)).toNat := by
    rw [word_toNat_lt', Challenge.EvmProof.Word.word_toNat_add c (t + x * y)]
    exact carry_split c.toNat (t + x * y).toNat hc hs1lt
  have hkey : ((UInt256.lt (c + (t + x * y)) c).toNat +
        ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat)) * 2 ^ 256 +
        (c + (t + x * y)).toNat =
      t.toNat + x.toNat * y.toNat + c.toNat := by
    calc ((UInt256.lt (c + (t + x * y)) c).toNat +
            ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat)) * 2 ^ 256 +
            (c + (t + x * y)).toNat
        = ((UInt256.lt (c + (t + x * y)) c).toNat * 2 ^ 256 +
              (c + (t + x * y)).toNat) +
            ((UInt256.lt (t + x * y) t).toNat * 2 ^ 256 +
              (mulHi x y).toNat * 2 ^ 256) := by ring
      _ = (c.toNat + (t + x * y).toNat) +
            ((UInt256.lt (t + x * y) t).toNat * 2 ^ 256 +
              (mulHi x y).toNat * 2 ^ 256) := by rw [← h2]
      _ = (((UInt256.lt (t + x * y) t).toNat * 2 ^ 256 + (t + x * y).toNat) +
              (mulHi x y).toNat * 2 ^ 256) + c.toNat := by ring
      _ = ((t.toNat + (x * y).toNat) + (mulHi x y).toNat * 2 ^ 256) + c.toNat := by
            rw [← h1]
      _ = t.toNat + ((mulHi x y).toNat * 2 ^ 256 + (x * y).toNat) + c.toNat := by ring
      _ = t.toNat + x.toNat * y.toNat + c.toNat := by rw [hprod]
  have hbound : t.toNat + x.toNat * y.toNat + c.toNat < 2 ^ 256 * 2 ^ 256 :=
    total_lt ht hx hy hc
  have hlt : (UInt256.lt (c + (t + x * y)) c).toNat +
      ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat) < 2 ^ 256 := by
    by_contra hcon
    have hcon' : 2 ^ 256 ≤ (UInt256.lt (c + (t + x * y)) c).toNat +
        ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat) := Nat.le_of_not_lt hcon
    have hstep : 2 ^ 256 * 2 ^ 256 ≤
        ((UInt256.lt (c + (t + x * y)) c).toNat +
          ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat)) * 2 ^ 256 :=
      Nat.mul_le_mul_right _ hcon'
    have hle : ((UInt256.lt (c + (t + x * y)) c).toNat +
        ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat)) * 2 ^ 256 ≤
        t.toNat + x.toNat * y.toNat + c.toNat := by
      rw [← hkey]
      exact Nat.le_add_right _ _
    exact absurd hbound (Nat.not_lt.mpr (Nat.le_trans hstep hle))
  have hcarryVal : (macCarry x y t c).toNat =
      (UInt256.lt (c + (t + x * y)) c).toNat +
        ((UInt256.lt (t + x * y) t).toNat + (mulHi x y).toNat) := by
    simp only [macCarry, Challenge.EvmProof.Word.word_toNat_add]
    rw [Nat.mod_eq_of_lt (show (UInt256.lt (t + x * y) t).toNat +
        (mulHi x y).toNat < 2 ^ 256 by omega), Nat.mod_eq_of_lt hlt]
  rw [hcarryVal]
  exact hkey

/-! Generic reassociation equalities from the promoted ERC661 foundation. -/
namespace MacAlt

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.EvmProof.Word

theorem mulMod_comm (a b : UInt256) :
    UInt256.mulMod b a maxWord = UInt256.mulMod a b maxWord := by
  apply word_ext
  rw [word_toNat_mulMod_max, word_toNat_mulMod_max, Nat.mul_comm]

theorem macSumNat (x y t c : UInt256) :
    (t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936
      = (c.toNat + (t.toNat + (x * y).toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  congr 1
  omega

/-- Wrapping subtraction reassociates: `a - (b - d) - e = a + (d - (e + b))`. -/
theorem subSubFold (a b d e : UInt256) :
    a - (b - d) - e = a + (d - (e + b)) := by
  apply word_ext
  have ha := word_lt_size a
  have hb := word_lt_size b
  have hd := word_lt_size d
  have he := word_lt_size e
  simp only [word_toNat_sub, word_toNat_add]
  omega

/-- The two carry bits of the reassociated sum add up to the same total. -/
theorem carryPair (x y t c : UInt256) :
    (if (t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936
       then 1 else 0) +
      (if ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < c.toNat then 1 else 0) =
    (UInt256.lt (c + (t + x * y)) c).toNat + (UInt256.lt (t + x * y) t).toNat := by
  have ha : (x * y).toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have h := word_lt_size (x * y); norm_num at h; exact h
  have hc : c.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have h := word_lt_size c; norm_num at h; exact h
  have ht : t.toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have h := word_lt_size t; norm_num at h; exact h
  simp only [word_toNat_lt', word_toNat_add,
    show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from by norm_num]
  obtain ⟨q1, r1, hq1, hr1, he1⟩ :
      ∃ q r, q ≤ 1 ∧ r < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧ (x * y).toNat + c.toNat = q * 115792089237316195423570985008687907853269984665640564039457584007913129639936 + r :=
    ⟨((x * y).toNat + c.toNat) / 115792089237316195423570985008687907853269984665640564039457584007913129639936, ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936,
      by omega, by omega, by omega⟩
  obtain ⟨q2, r2, hq2, hr2, he2⟩ :
      ∃ q r, q ≤ 1 ∧ r < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧ t.toNat + (x * y).toNat = q * 115792089237316195423570985008687907853269984665640564039457584007913129639936 + r :=
    ⟨(t.toNat + (x * y).toNat) / 115792089237316195423570985008687907853269984665640564039457584007913129639936, (t.toNat + (x * y).toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936,
      by omega, by omega, by omega⟩
  obtain ⟨q3, r3, hq3, hr3, he3⟩ :
      ∃ q r, q ≤ 1 ∧ r < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧ t.toNat + r1 = q * 115792089237316195423570985008687907853269984665640564039457584007913129639936 + r :=
    ⟨(t.toNat + r1) / 115792089237316195423570985008687907853269984665640564039457584007913129639936, (t.toNat + r1) % 115792089237316195423570985008687907853269984665640564039457584007913129639936, by omega, by omega, by omega⟩
  obtain ⟨q4, r4, hq4, hr4, he4⟩ :
      ∃ q r, q ≤ 1 ∧ r < 115792089237316195423570985008687907853269984665640564039457584007913129639936 ∧ c.toNat + r2 = q * 115792089237316195423570985008687907853269984665640564039457584007913129639936 + r :=
    ⟨(c.toNat + r2) / 115792089237316195423570985008687907853269984665640564039457584007913129639936, (c.toNat + r2) % 115792089237316195423570985008687907853269984665640564039457584007913129639936, by omega, by omega, by omega⟩
  have m1 : ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = r1 := by omega
  have m2 : (t.toNat + (x * y).toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = r2 := by omega
  have m3 : (t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = r3 := by omega
  have m4 : (c.toNat + r2) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = r4 := by omega
  rw [m1, m2, m3, m4]
  split_ifs <;> omega


theorem ifBit_toNat (P : Prop) [Decidable P] :
    (if P then (UInt256.ofNat 1) else UInt256.ofNat 0).toNat = if P then 1 else 0 := by
  split <;> simp

theorem bit_le (P : Prop) [Decidable P] : (if P then 1 else 0) ≤ 1 := by
  split <;> simp

/-- The carry the reassociated body computes is `macCarry`. -/
theorem macCarryFix (x y t c : UInt256) :
    (if (t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 then
        (UInt256.ofNat 1) else UInt256.ofNat 0) +
      (((if ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < c.toNat then (UInt256.ofNat 1)
            else UInt256.ofNat 0) -
          (UInt256.lt (UInt256.mulMod y x maxWord) (x * y) - UInt256.mulMod y x maxWord)) -
        x * y) =
      UInt256.lt (c + (t + x * y)) c + (UInt256.lt (t + x * y) t + mulHi x y) := by
  rw [mulMod_comm, subSubFold]
  have hp := carryPair x y t c
  have hH : (mulHi x y).toNat < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    have h := word_lt_size (mulHi x y); norm_num at h; exact h
  have hb1 := bit_le ((t.toNat + ((x * y).toNat + c.toNat)) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < ((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936)
  have hb2 := bit_le (((x * y).toNat + c.toNat) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 < c.toNat)
  apply word_ext
  simp only [word_toNat_add, ifBit_toNat, word_toNat_lt', mulHi,
    show (2 : Nat) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from by norm_num] at hp ⊢
  omega

end MacAlt

/-! ## Pointer walks

Every loop pointer walks downwards by one limb per iteration.  The EVM adds
the wrapped constant `2 ^ 256 - 32`, so the `j`-th pointer of a walk starting
at `base` is `UInt256.ofNat (ptrAt base j)`. -/

def ptrAt (base j : Nat) : Nat :=
  base + j * 115792089237316195423570985008687907853269984665640564039457584007913129639904

@[simp] theorem ptrAt_zero (base : Nat) : ptrAt base 0 = base := by
  simp [ptrAt]

theorem ptrAt_succ (base j : Nat) :
    115792089237316195423570985008687907853269984665640564039457584007913129639904 +
        ptrAt base j = ptrAt base (j + 1) := by
  simp only [ptrAt, Nat.succ_mul]
  omega

theorem ptrAt_toNat (base j : Nat) (hj : 32 * j ≤ base) (hbase : base < 2 ^ 256) :
    (UInt256.ofNat (ptrAt base j)).toNat = base - 32 * j := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, ptrAt]
  have hlit : (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      Nat) = 2 ^ 256 - 32 := by norm_num
  have hmul : j * 115792089237316195423570985008687907853269984665640564039457584007913129639904
      = j * 2 ^ 256 - 32 * j := by
    rw [hlit, Nat.mul_sub, Nat.mul_comm j 32]
  rw [hmul]
  have hrewrite : base + (j * 2 ^ 256 - 32 * j) = (base - 32 * j) + j * 2 ^ 256 := by
    have hle : 32 * j ≤ j * 2 ^ 256 := by
      have := Nat.mul_le_mul_right j (show 32 ≤ 2 ^ 256 by norm_num)
      omega
    omega
  rw [hrewrite, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

theorem ptrAt_mod (base j : Nat) (hj : 32 * j ≤ base) (hbase : base < 2 ^ 256) :
    ptrAt base j %
        115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      base - 32 * j := by
  have hlit : (115792089237316195423570985008687907853269984665640564039457584007913129639936 :
      Nat) = 2 ^ 256 := by norm_num
  rw [hlit, ← Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ptrAt_toNat base j hj hbase

/-! ## Active words

Every address `MONPRO` touches lies below `0x2500`, so once the setup block has
made `0x2500` bytes active no access here extends the high-water mark. -/

theorem activeWordsAfter_fix (curr off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9472) (hcurr : 296 ≤ curr) :
    MachineState.activeWordsAfter curr off sz = curr := by
  unfold MachineState.activeWordsAfter
  simp only [hsz, if_false]
  have hle : (off + sz - 1) / 32 + 1 ≤ curr := by omega
  exact Nat.max_eq_left hle

theorem activeWords_fix (s : State) (off sz : Nat) (hsz : sz ≠ 0)
    (hoff : off + sz ≤ 9472) (hact : 296 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat off sz) =
      s.activeWords := by
  rw [activeWordsAfter_fix _ off sz hsz hoff hact]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

/-! ## The CIOS memory model

Addresses (absolute, independent of the code offset):
`T_ = 8192` holds `t[n+1]`, `TN = 8224` holds `t[n]`, `TS = 8256` holds the
`n` limbs `t[n-1..0]` most significant first, so `t[k]` sits at
`8256 + 32 * (n - 1 - k)` and `TL = 8224 + 32 * n` is the address of `t[0]`.
`V_S32 = 9344`, `V_MINV = 9376`, `V_ML = 9408`, `V_TL = 9440`. -/

/-- Memory together with a running carry. -/
structure MacState where
  memory : ByteArray
  carry : UInt256

/-- The `b` limb consumed by row `i`. -/
def rowBi (mem : ByteArray) (pb n i : Nat) : UInt256 :=
  MachineState.readWord mem (pb + 32 * (n - 1 - i))

/-- Memory and carry after `j` steps of the first limb loop of a row:
step `j` accumulates `a[j] * b[i]` into `t[j]`. -/
def l1Step (mem : ByteArray) (bi : UInt256) (pa n : Nat) : Nat → MacState
  | 0 => ⟨mem, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := l1Step mem bi pa n j
      let x := MachineState.readWord prev.memory (pa + 32 * (n - 1 - j))
      let t := MachineState.readWord prev.memory (8256 + 32 * (n - 1 - j))
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded (macSum x bi t prev.carry).toNat 32)
          (8256 + 32 * (n - 1 - j))
        carry := macCarry x bi t prev.carry }

/-- `t[n] := t[n] + C`. -/
def midMem1 (mem : ByteArray) (c : UInt256) : ByteArray :=
  MachineState.writeBytes mem
    (Data.Bytes.natToBytesPadded (MachineState.readWord mem 8224 + c).toNat 32) 8224

/-- `t[n] := t[n] + C`, then `t[n+1] := carry`. -/
def midMem (mem : ByteArray) (c : UInt256) : ByteArray :=
  MachineState.writeBytes (midMem1 mem c)
    (Data.Bytes.natToBytesPadded
      (UInt256.lt (MachineState.readWord mem 8224 + c) c).toNat 32) 8192

/-- `mu = minv * t[0]` truncated to one limb. -/
def rowMu (mem : ByteArray) (n : Nat) : UInt256 :=
  MachineState.readWord mem 9376 * MachineState.readWord mem (8224 + 32 * n)

/-- The carry into the second limb loop: `t[0] + mu * m[0] = C * radix`. -/
def rowC0 (mem : ByteArray) (n : Nat) : UInt256 :=
  UInt256.isZero
      (UInt256.isZero (MachineState.readWord mem (32 * n - 32) * rowMu mem n)) +
    mulHi (MachineState.readWord mem (32 * n - 32)) (rowMu mem n)

theorem zero_lt_eq_double_isZero (x : UInt256) :
    UInt256.lt ({ val := 0 } : UInt256) x = UInt256.isZero (UInt256.isZero x) := by
  unfold UInt256.lt UInt256.isZero
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  by_cases h : x.toNat = 0
  · simp [h, hzero]
  · have hp : 0 < x.toNat := Nat.pos_of_ne_zero h
    simp [h, hzero, Nat.not_le_of_gt hp]

/-- Memory and carry after `k` steps of the second limb loop.  Step `k`
accumulates `m[k+1] * mu` into `t[k+1]` and stores the result one limb down. -/
def l2Step (mem : ByteArray) (mu c0 : UInt256) (n : Nat) : Nat → MacState
  | 0 => ⟨mem, c0⟩
  | k + 1 =>
      let prev := l2Step mem mu c0 n k
      let x := MachineState.readWord prev.memory (32 * (n - 2 - k))
      let t := MachineState.readWord prev.memory (8256 + 32 * (n - 2 - k))
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded (macSum x mu t prev.carry).toNat 32)
          (8256 + 32 * (n - 1 - k))
        carry := macCarry x mu t prev.carry }

/-- `t[n-1] := t[n] + C`. -/
def tailMem1 (mem : ByteArray) (c : UInt256) : ByteArray :=
  MachineState.writeBytes mem
    (Data.Bytes.natToBytesPadded (MachineState.readWord mem 8224 + c).toNat 32) 8256

/-- `t[n-1] := t[n] + C`, then `t[n] := t[n+1] + carry`. -/
def tailMem (mem : ByteArray) (c : UInt256) : ByteArray :=
  MachineState.writeBytes (tailMem1 mem c)
    (Data.Bytes.natToBytesPadded
      (MachineState.readWord (tailMem1 mem c) 8192 +
        UInt256.lt (MachineState.readWord mem 8224 + c) c).toNat 32) 8224

/-- The first limb loop of row `i`, run to completion. -/
def rowL1 (mem : ByteArray) (pa pb n i : Nat) : MacState :=
  l1Step mem (rowBi mem pb n i) pa n n

/-- Memory after the middle block of row `i`. -/
def rowMid (mem : ByteArray) (pa pb n i : Nat) : ByteArray :=
  midMem (rowL1 mem pa pb n i).memory (rowL1 mem pa pb n i).carry

/-- The second limb loop of row `i`, run to completion. -/
def rowL2 (mem : ByteArray) (pa pb n i : Nat) : MacState :=
  l2Step (rowMid mem pa pb n i) (rowMu (rowL1 mem pa pb n i).memory n)
    (rowC0 (rowL1 mem pa pb n i).memory n) n (n - 1)

/-- Memory after row `i`. -/
def rowMem (mem : ByteArray) (pa pb n i : Nat) : ByteArray :=
  tailMem (rowL2 mem pa pb n i).memory (rowL2 mem pa pb n i).carry

/-- Memory after `i` complete CIOS rows. -/
def rowsMem (mem : ByteArray) (pa pb n : Nat) : Nat → ByteArray
  | 0 => mem
  | i + 1 => rowMem (rowsMem mem pa pb n i) pa pb n i

/-- The prologue zeroes `t[n+1 .. 0]` with `CALLDATACOPY` from the end of the
calldata. -/
def mpZeroed (s : State) (mem : ByteArray) (n : Nat) : ByteArray :=
  MachineState.writeBytes mem
    (MachineState.readPadded s.executionEnv.calldata s.executionEnv.calldata.size
      (64 + 32 * n)) 8192

/-! ## States at the block boundaries

Loop heads carry their iteration index so the `iterateBounded` families are
indexed state functions; the block-exit states take the popped stack entries
as opaque parameters, which keeps every reduction lemma stated over an
arbitrary state constrained only by its `pc` and stack shape. -/

/-- Subroutine entry, pc 1939, stack `[pa, pb, pd, ret]`. -/
def mpEntryState (s : State) (mem : ByteArray) (pa pb : Nat) (pdst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1939
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

/-- The outer loop head, pc 1974, at the start of row `i`. -/
def mpOutState (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1974
           stack := [UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := mem }

/-- The first limb loop head, pc 1995, after `j` steps of row `i`. -/
def mpL1State (s : State) (mem : ByteArray) (bi : UInt256) (pa pb n i j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1995
           stack := [UInt256.ofNat (ptrAt (pa + 32 * n - 32) j),
                     UInt256.ofNat (ptrAt (8224 + 32 * n) j),
                     (l1Step mem bi pa n j).carry, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := (l1Step mem bi pa n j).memory }

/-- The row middle, pc 2141.  The two spent loop pointers are popped at once,
so they stay opaque. -/
def mpMidState (s : State) (mem : ByteArray) (paj ptj c bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2141
           stack := [paj, ptj, c, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := mem }

/-- The second limb loop head, pc 2241, after `k` steps of row `i`. -/
def mpL2State (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2241
           stack := [UInt256.ofNat (ptrAt (32 * n - 64) k),
                     UInt256.ofNat (ptrAt (8192 + 32 * n) k),
                     (l2Step mid mu c0 n k).carry, mu, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := (l2Step mid mu c0 n k).memory }

/-- The row tail, pc 2392. -/
def mpTailState (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2387
           stack := [pmj, ptj, c, mu, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), pdst, ret] ++ rest
           memory := mem }

/-- The subroutine exit, pc 2460, after all `n` rows. -/
def mpExitState (s : State) (mem : ByteArray) (pbi : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2425
           stack := [pbi, UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32),
                     pdst, ret] ++ rest
           memory := mem }

/-- `CSUB` entry, pc 2642, with stack `[pd, ret]`. -/
def mpCsubState (s : State) (mem : ByteArray) (pdst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2517
           stack := [pdst, ret] ++ rest
           memory := mem }


theorem maxWord_literal :
    (115792089237316195423570985008687907853269984665640564039457584007913129639935 :
      UInt256) = maxWord := rfl

end Challenge.Modexp.Submission.Proofs.Fast.Monpro
