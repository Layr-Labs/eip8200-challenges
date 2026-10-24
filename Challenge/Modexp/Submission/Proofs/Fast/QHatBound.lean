import Challenge.Modexp.Submission.Proofs.Limbs
import Challenge.EvmProof.Word
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option warningAsError false

/-!
# The quotient estimate never under-shoots

Pure arithmetic, no EVM and no memory.  Two facts about a schoolbook division
step whose dividend is split as `V = U * b^(k+1) + a2 * b^k + (< b^k)` and whose
divisor satisfies `m >= m0 * b^(k+1) + m1 * b^k`:

* `div_top_ge`  — the two-word-over-one-word estimate never under-shoots, with
  **no normalisation hypothesis**;
* `d3_gt`       — the classical correction criterion, proved by contradiction
  rather than cited.

Together they give `q >= V / m` for the estimator the artifact actually runs.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.QHat

open Nat

/-! ## Word-level bridge, at Nat level -/

theorem nested_div (U s dodd m0 : Nat) (hm : s * dodd = m0) :
    U / s / dodd = U / m0 := by rw [Nat.div_div_eq_div_mul, hm]

theorem inv_cancel (R W dodd dinv diff : Nat) (hdodd : 0 < dodd)
    (hW : W < dodd * R)
    (hinv : dodd * dinv ≡ 1 [MOD R])
    (hdiff : diff ≡ dodd * (W / dodd) [MOD R]) :
    dinv * diff % R = W / dodd := by
  have hchain : dinv * diff ≡ W / dodd [MOD R] :=
    calc dinv * diff ≡ dinv * (dodd * (W / dodd)) [MOD R] := Nat.ModEq.mul_left _ hdiff
      _ = (dodd * dinv) * (W / dodd) := by ring
      _ ≡ 1 * (W / dodd) [MOD R] := Nat.ModEq.mul_right (W / dodd) hinv
      _ = W / dodd := by ring
  have hlt : W / dodd < R := by
    exact Nat.div_lt_of_lt_mul hW
  have := hchain
  unfold Nat.ModEq at this
  rw [this, Nat.mod_eq_of_lt hlt]

/-- The two-word shift, no wrap. -/
theorem shift_split (R s t H L : Nat) (hs : 0 < s) (hst : s * t = R) :
    (H / s) * R + (t * (H % s) + L / s) = (H * R + L) / s := by
  have hdvd : s ∣ H * R := ⟨H * t, by rw [← hst]; ring⟩
  have h1 : (H * R + L) / s = H * R / s + L / s := Nat.add_div_of_dvd_right hdvd
  have h2 : H * R / s = H * t := by
    rw [← hst, show H * (s * t) = (H * t) * s by ring, Nat.mul_div_cancel _ hs]
  have h3 : (H / s) * R + t * (H % s) = H * t := by
    rw [← hst]
    have hdm := Nat.div_add_mod H s
    calc H / s * (s * t) + t * (H % s) = (s * (H / s) + H % s) * t := by ring
      _ = H * t := by rw [hdm]
  omega

/-- `lo - rho` computed in a word is congruent to `dodd * (W / dodd)`. -/
theorem diff_modeq (R W dodd hi lo rho : Nat) (hdodd : 0 < dodd)
    (hW : hi * R + lo = W) (hrho : rho = W % dodd) (hrR : rho ≤ R) :
    (lo + (R - rho)) ≡ dodd * (W / dodd) [MOD R] := by
  have hsplit : W - rho = dodd * (W / dodd) := by
    have h := Nat.div_add_mod W dodd; omega
  have hle : rho ≤ W := by rw [hrho]; exact Nat.mod_le _ _
  have key : (lo + (R - rho)) + hi * R = (W - rho) + R := by omega
  have h1 : (lo + (R - rho)) ≡ (lo + (R - rho)) + hi * R [MOD R] :=
    (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
      ⟨hi, by rw [Nat.add_sub_cancel_left]; ring⟩
  have h2 : (W - rho) + R ≡ (W - rho) [MOD R] :=
    ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
      ⟨1, by rw [Nat.add_sub_cancel_left]; ring⟩).symm
  rw [← hsplit]
  exact (h1.trans (by rw [key])).trans h2


/-! ## The lowest set bit, and the 2-adic split it certifies -/

theorem and_mod_two_of_even {a : Nat} (b : Nat) (ha : a % 2 = 0) : (a &&& b) % 2 = 0 := by
  have h0 : a.testBit 0 = false := by rw [Nat.testBit_zero]; simp [ha]
  have h : (a &&& b).testBit 0 = false := by rw [Nat.testBit_and, h0]; simp
  rw [Nat.testBit_zero] at h
  have h2 := Nat.mod_two_eq_zero_or_one (a &&& b)
  simp only [decide_eq_false_iff_not] at h
  omega

theorem and_mod_two_of_odd {a b : Nat} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    (a &&& b) % 2 = 1 := by
  have h0 : a.testBit 0 = true := by rw [Nat.testBit_zero]; simp [ha]
  have h1 : b.testBit 0 = true := by rw [Nat.testBit_zero]; simp [hb]
  have h : (a &&& b).testBit 0 = true := by rw [Nat.testBit_and, h0, h1]; simp
  rw [Nat.testBit_zero] at h
  simpa using h

/-- Complement within `k` bits: `g + f = 2^k - 1` forces disjoint bits. -/
theorem land_eq_zero_of_add : ∀ (k g f : Nat), g + f = 2^k - 1 → g &&& f = 0 := by
  intro k
  induction k with
  | zero => intro g f h; simp at h; rw [show g = 0 by omega, Nat.zero_and]
  | succ k ih =>
      intro g f h
      have hkpos : 1 ≤ 2^k := Nat.one_le_two_pow
      have hpow : 2^(k+1) = 2 * 2^k := by ring
      have hpar : g % 2 + f % 2 = 1 := by omega
      have hhalf : g/2 + f/2 = 2^k - 1 := by omega
      have hdiv : (g &&& f) / 2 = 0 := by rw [Nat.and_div_two]; exact ih _ _ hhalf
      have hmod : (g &&& f) % 2 = 0 := by
        rcases Nat.eq_zero_or_pos (g % 2) with h0 | h0
        · exact and_mod_two_of_even f h0
        · have hf0 : f % 2 = 0 := by omega
          rw [Nat.and_comm]; exact and_mod_two_of_even g hf0
      omega

/-- The lowest set bit, as `d &&& (2^m - d)`, together with the 2-adic split it certifies. -/
theorem lsb_spec : ∀ (m d : Nat), 0 < d → d < 2^m →
    ∃ v, v < m ∧ 2^v ∣ d ∧ (d / 2^v) % 2 = 1 ∧ d &&& (2^m - d) = 2^v := by
  intro m
  induction m with
  | zero => intro d hd hdm; simp at hdm; omega
  | succ m ih =>
      intro d hd hdm
      have hpow : 2^(m+1) = 2 * 2^m := by ring
      rcases Nat.even_or_odd d with he | ho
      · -- d even
        obtain ⟨e, rfl⟩ := he
        have he2 : 2 * e = e * 2 := by ring
        have hepos : 0 < e := by omega
        have helt : e < 2^m := by omega
        obtain ⟨v, hv, hdvd, hodd, hand⟩ := ih e hepos helt
        refine ⟨v + 1, by omega, ?_, ?_, ?_⟩
        · obtain ⟨c, rfl⟩ := hdvd; exact ⟨c, by ring⟩
        · rw [show (2:Nat)^(v+1) = 2 * 2^v by ring, show e + e = 2 * e by ring,
              Nat.mul_div_mul_left _ _ (by norm_num)]
          exact hodd
        · have hEE : e + e = 2 * e := by ring
          rw [hEE]
          have hsub : 2^(m+1) - 2 * e = 2 * (2^m - e) := by omega
          rw [hsub]
          have hd2 : ((2*e) &&& (2*(2^m - e))) / 2 = e &&& (2^m - e) := by
            rw [Nat.and_div_two]
            congr 1 <;> omega
          have hm2 : ((2*e) &&& (2*(2^m - e))) % 2 = 0 :=
            and_mod_two_of_even _ (by omega)
          rw [hand] at hd2
          rw [show (2:Nat)^(v+1) = 2 * 2^v by ring]
          omega
      · -- d odd
        have hdodd : d % 2 = 1 := Nat.odd_iff.mp ho
        refine ⟨0, by omega, by simp, by simpa using hdodd, ?_⟩
        set f := 2^(m+1) - d with hf
        have hfpos : 0 < f := by omega
        have hfodd : f % 2 = 1 := by omega
        have hhalf : d/2 + f/2 = 2^m - 1 := by
          have : 1 ≤ 2^m := Nat.one_le_two_pow
          omega
        have hdiv : (d &&& f) / 2 = 0 := by
          rw [Nat.and_div_two]; exact land_eq_zero_of_add m _ _ hhalf
        have hmod : (d &&& f) % 2 = 1 := and_mod_two_of_odd hdodd hfodd
        simp only [pow_zero]
        omega



/-- **Step 3.** `⌊U/m0⌋ ≥ ⌊V/m⌋` whenever `V < (U+1)·P` and `m0·P ≤ m`.
No normalisation of `m0` is needed: this is the direction the repair loop
cannot supply for itself. -/
theorem div_top_ge (V m U m0 P : Nat) (hm0 : 0 < m0) (hP : 0 < P)
    (hV : V < (U + 1) * P) (hm : m0 * P ≤ m) : V / m ≤ U / m0 := by
  have hmpos : 0 < m := lt_of_lt_of_le (Nat.mul_pos hm0 hP) hm
  have hcomm : P * m0 ≤ m := by rw [Nat.mul_comm]; exact hm
  have h1 : V / m ≤ V / (P * m0) := by
    apply Nat.div_le_div_left hcomm
    exact Nat.mul_pos hP hm0
  have h2 : V / (P * m0) = V / P / m0 := (Nat.div_div_eq_div_mul V P m0).symm
  have h3 : V / P ≤ U := by
    have h : V / P < U + 1 := by
      apply Nat.div_lt_of_lt_mul
      calc V < (U + 1) * P := hV
        _ = P * (U + 1) := by ring
    omega
  calc V / m ≤ V / (P * m0) := h1
    _ = V / P / m0 := h2
    _ ≤ U / m0 := Nat.div_le_div_right h3

/-- **Step 4.** The correction criterion, by direct contradiction.
If `q·m1 > r̂·b + a2` with `U = q·m0 + r̂`, then `q` is strictly above the true
quotient, so decrementing it once cannot take it below. -/
theorem d3_gt (V m U m0 m1 a2 q rhat b Q2 : Nat)
    (_hb : 0 < b) (_hQ2 : 0 < Q2)
    (hU : U = q * m0 + rhat)
    (hV : V < U * (b * Q2) + (a2 + 1) * Q2)
    (hm : m0 * (b * Q2) + m1 * Q2 ≤ m)
    (hd3 : rhat * b + a2 < q * m1) :
    V / m < q := by
  have hstep : U * b + a2 + 1 ≤ q * m0 * b + q * m1 := by
    subst hU
    have : (q * m0 + rhat) * b = q * m0 * b + rhat * b := by ring
    omega
  have hmul : V < q * m := by
    have h1 : (U * b + a2 + 1) * Q2 ≤ (q * m0 * b + q * m1) * Q2 :=
      Nat.mul_le_mul_right Q2 hstep
    have h2 : (q * m0 * b + q * m1) * Q2 = q * (m0 * (b * Q2) + m1 * Q2) := by ring
    have h3 : q * (m0 * (b * Q2) + m1 * Q2) ≤ q * m := Nat.mul_le_mul_left q hm
    have h4 : U * (b * Q2) + (a2 + 1) * Q2 = (U * b + a2 + 1) * Q2 := by ring
    omega
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hmul
    · exact h
  exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hmul; exact hmul)



/-! ## The raw estimate is the exact one-word quotient -/

/-- **The estimator, at Nat level.** With `s * t = R` (so `s` divides the radix) and
`s * dodd = m0`, the shifted pair `(H/s, lo)` divided by the odd part `dodd` through the
modular inverse is exactly `⌊(H·R+L)/m0⌋` — provided the quotient fits a word, which is
exactly the non-saturation test `H/s < dodd`. -/
theorem est_raw (R s t dodd m0 H L rho diff dinv : Nat)
    (hs : 0 < s) (ht : 0 < t) (hst : s * t = R) (hsm : s * dodd = m0) (hdodd : 0 < dodd)
    (hH : H < R) (hL : L < R) (hm0R : m0 < R) (hhi : H / s < dodd)
    (hrho : rho = ((H * R + L) / s) % dodd)
    (hdiff : diff ≡ (t * (H % s) + L / s) + (R - rho) [MOD R])
    (hinv : dodd * dinv ≡ 1 [MOD R]) :
    dinv * diff % R = (H * R + L) / m0 := by
  set lo := t * (H % s) + L / s with hlo
  have hsplit : (H / s) * R + lo = (H * R + L) / s := shift_split R s t H L hs hst
  have hmodlt : H % s < s := Nat.mod_lt _ hs
  have hloR : lo < R := by
    have h1 : t * (H % s) ≤ t * (s - 1) := Nat.mul_le_mul_left t (by omega)
    have h2 : L / s < t := Nat.div_lt_of_lt_mul (by rw [hst]; exact hL)
    have h3 : t * (s - 1) = R - t := by
      rw [← hst, Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    have htR : t ≤ R := by rw [← hst]; exact Nat.le_mul_of_pos_left t hs
    omega
  have hWlt : (H * R + L) / s < dodd * R := by
    rw [← hsplit]
    have : (H / s) * R + lo < dodd * R := by
      have hk : (H / s) + 1 ≤ dodd := hhi
      have : ((H / s) + 1) * R ≤ dodd * R := Nat.mul_le_mul_right R hk
      nlinarith [hloR]
    exact this
  have hd : diff ≡ dodd * (((H * R + L) / s) / dodd) [MOD R] :=
    hdiff.trans (diff_modeq R ((H * R + L) / s) dodd (H / s) lo rho hdodd hsplit hrho
      (by
        have hdm : dodd ≤ m0 := by rw [← hsm]; exact Nat.le_mul_of_pos_left dodd hs
        have : rho < dodd := by rw [hrho]; exact Nat.mod_lt _ hdodd
        omega))
  rw [inv_cancel R ((H * R + L) / s) dodd dinv diff hdodd hWlt hinv hd]
  exact nested_div (H * R + L) s dodd m0 hsm

/-! ## The truncated correction test implies the classical one -/

/-- The artifact compares `⌊q/2^128⌋ · ⌊m1/2^128⌋` against `r̂`.  Because both factors
lose at most their low half, the product it tests is at most `q·m1 / R`, so firing
forces a full radix of slack — more than the `a2` the classical test carries. -/
theorem trunc_gt (R h q m1 rhat a2 : Nat) (hR : h * h = R) (ha2 : a2 < R)
    (hc : rhat < (q / h) * (m1 / h)) : rhat * R + a2 < q * m1 := by
  have h1 : h * (q / h) ≤ q := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self q h
  have h2 : h * (m1 / h) ≤ m1 := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self m1 h
  have h3 : (h * (q / h)) * (h * (m1 / h)) ≤ q * m1 := Nat.mul_le_mul h1 h2
  have h4 : (h * (q / h)) * (h * (m1 / h)) = R * ((q / h) * (m1 / h)) := by
    rw [← hR]; ring
  have h5 : R * (rhat + 1) ≤ R * ((q / h) * (m1 / h)) := Nat.mul_le_mul_left R (by omega)
  have h6 : R * (rhat + 1) = rhat * R + R := by ring
  omega

/-! ## The estimator never under-shoots -/

/-- **The whole lower bound, at Nat level, all three branches.**
`qfin` is the artifact's final quotient: the raw estimate, decremented when `cond`
fires, or saturated to `R - 1` when the raw quotient would not fit a word. -/
theorem est_ge (R s t dodd m0 m1 a2 H L V m rho diff dinv Q2 qfin : Nat) (cond : Bool)
    (hs : 0 < s) (ht : 0 < t) (hst : s * t = R) (hsm : s * dodd = m0) (hdodd : 0 < dodd)
    (hH : H < R) (hL : L < R) (hm0R : m0 < R) (hQ2 : 0 < Q2) (hm0 : 0 < m0)
    (hrho : rho = ((H * R + L) / s) % dodd)
    (hdiff : diff ≡ (t * (H % s) + L / s) + (R - rho) [MOD R])
    (hinv : dodd * dinv ≡ 1 [MOD R])
    (hV : V < (H * R + L) * (R * Q2) + (a2 + 1) * Q2)
    (hVP : V < ((H * R + L) + 1) * (R * Q2))
    (hm : m0 * (R * Q2) + m1 * Q2 ≤ m)
    (hmP : m0 * (R * Q2) ≤ m)
    (hQlt : V / m < R)
    (hcond : H / s < dodd → cond = true →
      (H * R + L) % m0 * R + a2 < (dinv * diff % R) * m1)
    (hqfin : qfin = if H / s < dodd
                    then (dinv * diff % R) - (if cond then 1 else 0)
                    else R - 1) :
    V / m ≤ qfin := by
  by_cases hsat : H / s < dodd
  · have hraw : dinv * diff % R = (H * R + L) / m0 :=
      est_raw R s t dodd m0 H L rho diff dinv hs ht hst hsm hdodd hH hL hm0R hsat hrho hdiff hinv
    have hbase : V / m ≤ (H * R + L) / m0 :=
      div_top_ge V m (H * R + L) m0 (R * Q2) hm0 (Nat.mul_pos (by omega) hQ2) hVP hmP
    rw [hqfin, if_pos hsat]
    cases hc : cond with
    | false => rw [hraw]; simpa using hbase
    | true =>
        have hstrict : V / m < dinv * diff % R := by
          refine d3_gt V m (H * R + L) m0 m1 a2 (dinv * diff % R) ((H * R + L) % m0)
            R Q2 (by omega) hQ2 ?_ hV hm (hcond hsat hc)
          rw [hraw]; exact (Nat.div_add_mod' (H * R + L) m0).symm
        simp only [hc, if_true]
        omega
  · rw [hqfin, if_neg hsat]; omega


/-! ## Word-level wrappers -/

open EvmSemantics (UInt256)
open Challenge.EvmProof.Word

theorem toNat_div (a b : UInt256) : (a / b).toNat = a.toNat / b.toNat := by
  show (UInt256.div a b).toNat = _
  unfold UInt256.div
  by_cases hb : b.val.val = 0
  · rw [if_pos hb]
    have : b.toNat = 0 := hb
    rw [this]; simp [UInt256.toNat]
  · rw [if_neg hb]
    show (a.val / b.val).val = _
    exact Fin.div_val a.val b.val

theorem toNat_mulMod (a b n : UInt256) (hn : n.toNat ≠ 0) :
    (UInt256.mulMod a b n).toNat = a.toNat * b.toNat % n.toNat := by
  unfold UInt256.mulMod
  rw [if_neg (by simpa [UInt256.toNat] using hn), word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero hn))
    (Nat.le_of_lt n.val.isLt))

theorem toNat_addMod (a b n : UInt256) (hn : n.toNat ≠ 0) :
    (UInt256.addMod a b n).toNat = (a.toNat + b.toNat) % n.toNat := by
  unfold UInt256.addMod
  rw [if_neg (by simpa [UInt256.toNat] using hn), word_toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero hn))
    (Nat.le_of_lt n.val.isLt))

theorem toNat_gt (a b : UInt256) :
    (UInt256.gt a b).toNat = if b.toNat < a.toNat then 1 else 0 := by
  unfold UInt256.gt
  split <;> simp_all [word_toNat_ofNat]

/-- `land d (0 - d)` is the lowest set bit of a nonzero word. -/
theorem lsb_word (d : UInt256) (hd : d.toNat ≠ 0) :
    ∃ v, v < 256 ∧ (UInt256.land d (UInt256.ofNat 0 - d)).toNat = 2 ^ v ∧
      2 ^ v ∣ d.toNat ∧ (d.toNat / 2 ^ v) % 2 = 1 := by
  have hlt : d.toNat < 2 ^ 256 := d.val.isLt
  have hneg : (UInt256.ofNat 0 - d).toNat = 2 ^ 256 - d.toNat := by
    rw [word_toNat_sub, word_toNat_ofNat]
    have : (0 : Nat) % 2 ^ 256 = 0 := by norm_num
    rw [this, Nat.add_zero]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨v, hv, hdvd, hodd, hand⟩ := lsb_spec 256 d.toNat (Nat.pos_of_ne_zero hd) hlt
  exact ⟨v, hv, by rw [word_toNat_land, hneg]; exact hand, hdvd, hodd⟩


/-! ## Two small facts the word layer needs -/

/-- `X * H` in a word, with `X = R / s`, is exactly `t * (H % s)`: the multiply by the
scaled radix keeps only the low bits of `H`, and the result cannot wrap. -/
theorem mul_shift_mod (R s t H : Nat) (hs : 0 < s) (ht : 0 < t) (hst : s * t = R) :
    (t * H) % R = t * (H % s) := by
  have hdm := Nat.div_add_mod H s
  have hkey : t * H = R * (H / s) + t * (H % s) := by
    calc t * H = t * (s * (H / s) + H % s) := by rw [hdm]
      _ = (s * t) * (H / s) + t * (H % s) := by ring
      _ = R * (H / s) + t * (H % s) := by rw [hst]
  have hlt : t * (H % s) < R := by
    have h1 : H % s < s := Nat.mod_lt _ hs
    have h2 : t * (H % s) < t * s := Nat.mul_lt_mul_of_pos_left h1 ht
    rw [Nat.mul_comm t s, hst] at h2
    exact h2
  rw [hkey, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

/-- `(R - dodd) % dodd = R % dodd`: what `preBmod` stores really is `R mod dodd`. -/
theorem sub_mod_self (R dodd : Nat) (hd : 0 < dodd) (hle : dodd ≤ R) :
    (R - dodd) % dodd = R % dodd := by
  conv_rhs => rw [show R = (R - dodd) + dodd by omega]
  rw [Nat.add_mod_right]


/-- Saturation: OR-ing with the all-ones word swallows everything below the radix. -/
theorem or_two_pow_sub_one (k a : Nat) (ha : a < 2 ^ k) : (2 ^ k - 1) ||| a = 2 ^ k - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow_sub_one]
  by_cases hik : i < k
  · simp [hik]
  · have hfalse : a.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      exact lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [hik, hfalse]

end Challenge.Modexp.Submission.Proofs.Fast.QHat
