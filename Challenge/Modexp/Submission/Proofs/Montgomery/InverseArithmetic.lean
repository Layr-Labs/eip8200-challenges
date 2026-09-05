import Challenge.EvmProof.Word
import Mathlib.Tactic

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Montgomery.InverseArithmetic

open EvmSemantics

private def B : Nat := 2 ^ 256

def seed (m : UInt256) : UInt256 :=
  UInt256.xor (3 * m) 2

def refine (m v : UInt256) : UInt256 :=
  v * (2 - m * v)

def inverse (m : UInt256) : UInt256 :=
  refine m (refine m (refine m (refine m (refine m (refine m (seed m))))))

def nprime (m : UInt256) : UInt256 :=
  0 - inverse m

private theorem B_pos : 0 < B := by
  norm_num [B]

private theorem pow_dvd_B {k : Nat} (hk : k ≤ 256) : 2 ^ k ∣ B := by
  simpa [B] using Nat.pow_dvd_pow 2 hk

private theorem word_toNat_mul (x y : UInt256) :
    (x * y).toNat = (x.toNat * y.toNat) % B := by
  change (x.val * y.val).val = _
  rw [Fin.val_mul]
  rfl

private theorem word_toNat_xor (x y : UInt256) :
    (UInt256.xor x y).toNat = x.toNat ^^^ y.toNat := by
  exact Fin.xor_val_of_two_pow (w := 256) x.val y.val

private theorem word_mul_modEq (k : Nat) (hk : k ≤ 256) (x y : UInt256) :
    (x * y).toNat ≡ x.toNat * y.toNat [MOD 2 ^ k] := by
  rw [word_toNat_mul]
  exact Nat.ModEq.of_dvd (pow_dvd_B hk) (Nat.mod_modEq _ B)

private theorem cast_mod_B {k : Nat} (hk : k ≤ 256) (a : Nat) :
    ((a % B : Nat) : ZMod (2 ^ k)) = (a : ZMod (2 ^ k)) := by
  apply (ZMod.natCast_eq_natCast_iff (a % B) a (2 ^ k)).2
  exact Nat.ModEq.of_dvd (pow_dvd_B hk) (Nat.mod_modEq a B)

private theorem cast_B_zero {k : Nat} (hk : k ≤ 256) :
    (B : ZMod (2 ^ k)) = 0 := by
  have h : (B : ZMod (2 ^ k)) = (0 : Nat) := by
    apply (ZMod.natCast_eq_natCast_iff B 0 (2 ^ k)).2
    rw [Nat.modEq_zero_iff_dvd]
    exact pow_dvd_B hk
  simpa using h

private theorem word_cast_mul {k : Nat} (hk : k ≤ 256) (x y : UInt256) :
    ((x * y).toNat : ZMod (2 ^ k)) =
      (x.toNat : ZMod (2 ^ k)) * (y.toNat : ZMod (2 ^ k)) := by
  rw [← Nat.cast_mul]
  apply (ZMod.natCast_eq_natCast_iff _ _ (2 ^ k)).2
  exact word_mul_modEq k hk x y

private theorem word_cast_sub {k : Nat} (hk : k ≤ 256) (x y : UInt256) :
    ((x - y).toNat : ZMod (2 ^ k)) =
      (x.toNat : ZMod (2 ^ k)) - (y.toNat : ZMod (2 ^ k)) := by
  rw [Challenge.EvmProof.Word.word_toNat_sub]
  change (((B + x.toNat - y.toNat) % B : Nat) : ZMod (2 ^ k)) = _
  rw [cast_mod_B hk]
  rw [Nat.cast_sub]
  · rw [Nat.cast_add, cast_B_zero hk]
    simp
  · have hy : y.toNat < B := y.val.isLt
    omega

private theorem seed_modEq_four (m : UInt256) :
    (seed m).toNat ≡ (3 * m.toNat ^^^ 2) [MOD 2 ^ 4] := by
  have h3 : (3 : UInt256).toNat = 3 := by
    change 3 % 2 ^ 256 = 3
    norm_num
  have h2 : (2 : UInt256).toNat = 2 := by
    change 2 % 2 ^ 256 = 2
    norm_num
  have hmod : (3 * m.toNat % B) % 2 ^ 4 = (3 * m.toNat) % 2 ^ 4 := by
    exact Nat.mod_mod_of_dvd _ (pow_dvd_B (by norm_num))
  unfold seed
  rw [word_toNat_xor, word_toNat_mul, h3, h2]
  change ((3 * m.toNat % B) ^^^ 2) % 2 ^ 4 =
    (3 * m.toNat ^^^ 2) % 2 ^ 4
  rw [Nat.xor_mod_two_pow]
  rw [hmod]
  rw [Nat.xor_mod_two_pow]

private theorem seed_mod_four (m : UInt256) :
    (seed m).toNat % 16 =
      (3 * (m.toNat % 16) ^^^ 2) % 16 := by
  have hfull : (seed m).toNat % 16 = (3 * m.toNat ^^^ 2) % 16 := by
    simpa [Nat.ModEq] using seed_modEq_four m
  rw [hfull]
  change (3 * m.toNat ^^^ 2) % (2 ^ 4) =
    (3 * (m.toNat % 16) ^^^ 2) % (2 ^ 4)
  rw [Nat.xor_mod_two_pow]
  rw [Nat.mul_mod]
  rw [Nat.xor_mod_two_pow]

private theorem seed_residue_inverse (r : Nat) (hr : r < 16)
    (hodd : r % 2 = 1) : (r * (3 * r ^^^ 2)) % 16 = 1 := by
  interval_cases r <;> norm_num at hodd
  all_goals decide

private theorem seed_inverse (m : UInt256) (hodd : m.toNat % 2 = 1) :
    m.toNat * (seed m).toNat ≡ 1 [MOD 2 ^ 4] := by
  have hr : m.toNat % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hrodd : (m.toNat % 16) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 16), hodd]
  have hres := seed_residue_inverse (m.toNat % 16) hr hrodd
  change (m.toNat * (seed m).toNat) % 16 = 1
  rw [Nat.mul_mod, seed_mod_four]
  simpa [Nat.mul_mod] using hres

private theorem refine_cast {k : Nat} (hk : k ≤ 256) (m v : UInt256) :
    ((refine m v).toNat : ZMod (2 ^ k)) =
      (v.toNat : ZMod (2 ^ k)) *
        (2 - (m.toNat : ZMod (2 ^ k)) * (v.toNat : ZMod (2 ^ k))) := by
  unfold refine
  rw [word_cast_mul hk, word_cast_sub hk, word_cast_mul hk]
  have h2 : (2 : UInt256).toNat = 2 := by
    change 2 % 2 ^ 256 = 2
    norm_num
  rw [h2]
  norm_num

private theorem refine_correct {k : Nat} (hk : 0 < k) (h2k : 2 * k ≤ 256)
    (m v : UInt256)
    (hgood : m.toNat * v.toNat ≡ 1 [MOD 2 ^ k]) :
    m.toNat * (refine m v).toNat ≡ 1 [MOD 2 ^ (2 * k)] := by
  have hKone : 1 < 2 ^ k := Nat.one_lt_pow (Nat.ne_of_gt hk) (by norm_num)
  have hprod_pos : 0 < m.toNat * v.toNat := by
    by_contra h
    have hz : m.toNat * v.toNat = 0 := Nat.eq_zero_of_not_pos h
    have hbad := hgood
    rw [hz] at hbad
    change 0 % 2 ^ k = 1 % 2 ^ k at hbad
    rw [Nat.zero_mod, Nat.mod_eq_of_lt hKone] at hbad
    omega
  have hdiv : 2 ^ k ∣ m.toNat * v.toNat - 1 :=
    (Nat.modEq_iff_dvd' (Nat.succ_le_of_lt hprod_pos)).mp hgood.symm
  rcases hdiv with ⟨q, hq⟩
  have hprod : m.toNat * v.toNat = 1 + 2 ^ k * q := by
    omega
  have hpow : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hKsq :
      ((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) *
          ((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) = 0 := by
    calc
      ((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) *
          ((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) =
          ((2 ^ k * 2 ^ k : Nat) : ZMod (2 ^ (2 * k))) := by
            rw [Nat.cast_mul]
      _ = ((2 ^ (2 * k) : Nat) : ZMod (2 ^ (2 * k))) := by
            rw [hpow]
      _ = 0 := by simp
  have hmv :
      (m.toNat : ZMod (2 ^ (2 * k))) * (v.toNat : ZMod (2 ^ (2 * k))) =
        1 + ((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) * (q : ZMod (2 ^ (2 * k))) := by
    calc
      (m.toNat : ZMod (2 ^ (2 * k))) * (v.toNat : ZMod (2 ^ (2 * k))) =
          ((m.toNat * v.toNat : Nat) : ZMod (2 ^ (2 * k))) := by
            rw [Nat.cast_mul]
      _ = ((1 + 2 ^ k * q : Nat) : ZMod (2 ^ (2 * k))) := by
            rw [hprod]
      _ = 1 + ((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) *
            (q : ZMod (2 ^ (2 * k))) := by
            norm_num
  have hqq :
      (((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) * (q : ZMod (2 ^ (2 * k)))) *
        (((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) * (q : ZMod (2 ^ (2 * k)))) = 0 := by
    calc
      (((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) * (q : ZMod (2 ^ (2 * k)))) *
          (((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) * (q : ZMod (2 ^ (2 * k)))) =
          (((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) *
              ((2 ^ k : Nat) : ZMod (2 ^ (2 * k)))) *
            ((q : ZMod (2 ^ (2 * k))) * (q : ZMod (2 ^ (2 * k)))) := by ring
      _ = 0 := by rw [hKsq, zero_mul]
  have hz :
      ((m.toNat * (refine m v).toNat : Nat) : ZMod (2 ^ (2 * k))) = 1 := by
    rw [Nat.cast_mul, refine_cast h2k]
    calc
      (m.toNat : ZMod (2 ^ (2 * k))) *
          ((v.toNat : ZMod (2 ^ (2 * k))) *
            (2 - (m.toNat : ZMod (2 ^ (2 * k))) * (v.toNat : ZMod (2 ^ (2 * k))))) =
          ((m.toNat : ZMod (2 ^ (2 * k))) * (v.toNat : ZMod (2 ^ (2 * k)))) *
            (2 - (m.toNat : ZMod (2 ^ (2 * k))) * (v.toNat : ZMod (2 ^ (2 * k)))) := by ring
      _ = (1 + ((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) *
            (q : ZMod (2 ^ (2 * k)))) *
            (2 - (1 + ((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) *
              (q : ZMod (2 ^ (2 * k))))) := by
              rw [hmv]
      _ = 1 - (((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) *
          (q : ZMod (2 ^ (2 * k)))) *
            (((2 ^ k : Nat) : ZMod (2 ^ (2 * k))) *
              (q : ZMod (2 ^ (2 * k)))) := by ring
      _ = 1 := by rw [hqq]; simp
  have hz' :
      ((m.toNat * (refine m v).toNat : Nat) : ZMod (2 ^ (2 * k))) =
        ((1 : Nat) : ZMod (2 ^ (2 * k))) := by
    simpa only [Nat.cast_one] using hz
  exact (ZMod.natCast_eq_natCast_iff _ _ (2 ^ (2 * k))).mp hz'

private theorem inverse_correct (m : UInt256) (hodd : m.toNat % 2 = 1) :
    m.toNat * (inverse m).toNat ≡ 1 [MOD 2 ^ 256] := by
  have h4 := seed_inverse m hodd
  have h8 := refine_correct (k := 4) (by norm_num) (by norm_num)
    m (seed m) h4
  have h16 := refine_correct (k := 8) (by norm_num) (by norm_num)
    m (refine m (seed m)) h8
  have h32 := refine_correct (k := 16) (by norm_num) (by norm_num)
    m (refine m (refine m (seed m))) h16
  have h64 := refine_correct (k := 32) (by norm_num) (by norm_num)
    m (refine m (refine m (refine m (seed m)))) h32
  have h128 := refine_correct (k := 64) (by norm_num) (by norm_num)
    m (refine m (refine m (refine m (refine m (seed m))))) h64
  have h256 := refine_correct (k := 128) (by norm_num) (by norm_num)
    m (refine m (refine m (refine m (refine m (refine m (seed m)))))) h128
  simpa [inverse] using h256

theorem nprime_correct (m : UInt256) (hodd : m.toNat % 2 = 1) :
    (m.toNat * (nprime m).toNat + 1) % (2 ^ 256) = 0 := by
  have hinv := inverse_correct m hodd
  have hmul :
      (m.toNat : ZMod B) * ((inverse m).toNat : ZMod B) = 1 := by
    have hcast :
        ((m.toNat * (inverse m).toNat : Nat) : ZMod B) =
          ((1 : Nat) : ZMod B) :=
      (ZMod.natCast_eq_natCast_iff _ _ B).mpr hinv
    simpa only [Nat.cast_mul, Nat.cast_one] using hcast
  have hnprime : ((nprime m).toNat : ZMod B) =
      -((inverse m).toNat : ZMod B) := by
    have hzero : (0 : UInt256).toNat = 0 := by
      change 0 % 2 ^ 256 = 0
      norm_num
    have hsub := word_cast_sub (k := 256) (by norm_num)
      (0 : UInt256) (inverse m)
    change (((0 : UInt256) - inverse m).toNat : ZMod (2 ^ 256)) =
      -((inverse m).toNat : ZMod (2 ^ 256))
    rw [hsub, hzero]
    ring
  have hz :
      ((m.toNat * (nprime m).toNat + 1 : Nat) : ZMod B) = 0 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul, hnprime]
    calc
      (m.toNat : ZMod B) * -((inverse m).toNat : ZMod B) + 1 =
          -((m.toNat : ZMod B) * ((inverse m).toNat : ZMod B)) + 1 := by ring
      _ = 0 := by rw [hmul]; ring
  have hmod : m.toNat * (nprime m).toNat + 1 ≡ 0 [MOD B] :=
    (ZMod.natCast_eq_natCast_iff _ _ B).mp hz
  simpa [B, Nat.ModEq] using hmod

end Challenge.Modexp.Submission.Proofs.Montgomery.InverseArithmetic
