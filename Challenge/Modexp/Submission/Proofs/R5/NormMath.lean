import Challenge.Modexp.Submission.Proofs.R5.Digits
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-!
# The trial subtraction of the r5 normalization

`t0 = a0 - n0`, `t(i+1) = (a(i+1) - s i) - n(i+1)` with the borrow `s i = t i >> 255` and the
digit `d i = t i & (2^240 - 1)`. For digits below `2^240` (top digits below `2^65`) the top
borrow is `1` exactly when `T < N`, and otherwise the digits are those of `T - N`.
-/

namespace CycleSubmission.R5.NormMath
open EvmSemantics Challenge.EvmProof.Word
open CycleSubmission.R5.Digits

def bor (a n s : Nat) : Nat := if n + s ≤ a then 0 else 1

theorem sub_toNat (a b : UInt256) (hle : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  rw [word_toNat_sub_cond, if_neg (by omega)]

theorem sub_toNat_neg (a b : UInt256) (hlt : a.toNat < b.toNat) : (a - b).toNat = 2^256 + a.toNat - b.toNat := by
  rw [word_toNat_sub_cond, if_pos hlt]

theorem shr255 (t : UInt256) : (UInt256.shiftRight t (UInt256.ofNat 255)).toNat = t.toNat / 2^255 := by
  rw [shiftRight_toNat _ (by decide), Nat.shiftRight_eq_div_pow]

/-- One borrow step `t = (a - s) - n` (with `s ≤ 1`, all below `2^241`). -/
theorem step (a s n : UInt256) (ha : a.toNat < 2^241) (hn : n.toNat < 2^241) (hs : s.toNat ≤ 1) :
    (UInt256.shiftRight ((a - s) - n) (UInt256.ofNat 255)).toNat = bor a.toNat n.toNat s.toNat ∧
    ((a - s) - n).toNat + n.toNat + s.toNat = a.toNat + 2^256 * bor a.toNat n.toNat s.toNat := by
  unfold bor
  rw [shr255]
  by_cases h : n.toNat + s.toNat ≤ a.toNat
  · rw [if_pos h]
    have h1 : (a - s).toNat = a.toNat - s.toNat := sub_toNat _ _ (by omega)
    have h2 : ((a - s) - n).toNat = a.toNat - s.toNat - n.toNat := by
      rw [sub_toNat _ _ (by omega), h1]
    rw [h2]
    refine ⟨?_, by omega⟩
    apply Nat.div_eq_of_lt
    omega
  · rw [if_neg h]
    by_cases hs0 : s.toNat ≤ a.toNat
    · have h1 : (a - s).toNat = a.toNat - s.toNat := sub_toNat _ _ hs0
      have h2 : ((a - s) - n).toNat = 2^256 + (a.toNat - s.toNat) - n.toNat := by
        rw [sub_toNat_neg _ _ (by omega), h1]
      rw [h2]
      refine ⟨?_, by omega⟩
      apply Nat.div_eq_of_lt_le <;> omega
    · have h1 : (a - s).toNat = 2^256 + a.toNat - s.toNat := sub_toNat_neg _ _ (by omega)
      have h2 : ((a - s) - n).toNat = 2^256 + a.toNat - s.toNat - n.toNat := by
        rw [sub_toNat _ _ (by omega), h1]
      rw [h2]
      refine ⟨?_, by omega⟩
      apply Nat.div_eq_of_lt_le <;> omega

/-- The first step `t0 = a0 - n0`. -/
theorem step0 (a n : UInt256) (ha : a.toNat < 2^241) (hn : n.toNat < 2^241) :
    (UInt256.shiftRight (a - n) (UInt256.ofNat 255)).toNat = bor a.toNat n.toNat 0 ∧
    (a - n).toNat + n.toNat = a.toNat + 2^256 * bor a.toNat n.toNat 0 := by
  unfold bor
  rw [shr255]
  by_cases h : n.toNat ≤ a.toNat
  · rw [if_pos (by omega), sub_toNat _ _ h]
    refine ⟨?_, by omega⟩
    apply Nat.div_eq_of_lt; omega
  · rw [if_neg (by omega), sub_toNat_neg _ _ (by omega)]
    refine ⟨?_, by omega⟩
    apply Nat.div_eq_of_lt_le <;> omega

/-- The masked digit of a step: `d = t mod 2^240`, and `d + n + s = a + 2^240 * borrow`. -/
theorem digit (t a n s b : Nat) (ht : t + n + s = a + 2^256 * b) (hb : b ≤ 1) (ht256 : t < 2^256)
    (ha : a < 2^240) (hn : n < 2^240) (hs : s ≤ 1) :
    t % 2^240 + n + s = a + 2^240 * b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · have : t < 2^240 := by omega
    rw [Nat.mod_eq_of_lt this]; omega
  · have hu : 2^240 + a - n - s < 2^240 := by omega
    have ht' : t = (2^240 + a - n - s) + 2^240 * (2^16 - 1) := by omega
    rw [ht', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
    omega

/-- The whole trial subtraction. Digits below `2^240`, top digits below `2^65`; the chain words
`t i` are named by equations so that every step fact speaks about the same atoms. -/
theorem chain (a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 t0 t1 t2 t3 t4 : UInt256)
    (ht0 : t0 = a0 - n0)
    (ht1 : t1 = (a1 - UInt256.shiftRight t0 (UInt256.ofNat 255)) - n1)
    (ht2 : t2 = (a2 - UInt256.shiftRight t1 (UInt256.ofNat 255)) - n2)
    (ht3 : t3 = (a3 - UInt256.shiftRight t2 (UInt256.ofNat 255)) - n3)
    (ht4 : t4 = (a4 - UInt256.shiftRight t3 (UInt256.ofNat 255)) - n4)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (ha4 : a4.toNat < 2^65)
    (hn0 : n0.toNat < 2^240) (hn1 : n1.toNat < 2^240) (hn2 : n2.toNat < 2^240) (hn3 : n3.toNat < 2^240)
    (hn4 : n4.toNat < 2^65) :
    ((UInt256.shiftRight t4 (UInt256.ofNat 255)).toNat =
      if n0.toNat + n1.toNat * 2^240 + n2.toNat * 2^480 + n3.toNat * 2^720 + n4.toNat * 2^960 ≤
        a0.toNat + a1.toNat * 2^240 + a2.toNat * 2^480 + a3.toNat * 2^720 + a4.toNat * 2^960 then 0 else 1) ∧
    (n0.toNat + n1.toNat * 2^240 + n2.toNat * 2^480 + n3.toNat * 2^720 + n4.toNat * 2^960 ≤
        a0.toNat + a1.toNat * 2^240 + a2.toNat * 2^480 + a3.toNat * 2^720 + a4.toNat * 2^960 →
      (UInt256.land M t0).toNat + (UInt256.land M t1).toNat * 2^240 +
        (UInt256.land M t2).toNat * 2^480 + (UInt256.land M t3).toNat * 2^720 + t4.toNat * 2^960 =
        (a0.toNat + a1.toNat * 2^240 + a2.toNat * 2^480 + a3.toNat * 2^720 + a4.toNat * 2^960) -
        (n0.toNat + n1.toNat * 2^240 + n2.toNat * 2^480 + n3.toNat * 2^720 + n4.toNat * 2^960) ∧
      (UInt256.land M t0).toNat < 2^240 ∧ (UInt256.land M t1).toNat < 2^240 ∧
      (UInt256.land M t2).toNat < 2^240 ∧ (UInt256.land M t3).toNat < 2^240 ∧ t4.toNat < 2^65) := by
  obtain ⟨e0s, e0v⟩ := step0 a0 n0 (by omega) (by omega)
  rw [← ht0] at e0s e0v
  have hb0 : (UInt256.shiftRight t0 (UInt256.ofNat 255)).toNat ≤ 1 := by rw [e0s]; unfold bor; split <;> omega
  obtain ⟨e1s, e1v⟩ := step a1 (UInt256.shiftRight t0 (UInt256.ofNat 255)) n1 (by omega) (by omega) hb0
  rw [← ht1] at e1s e1v
  have hb1 : (UInt256.shiftRight t1 (UInt256.ofNat 255)).toNat ≤ 1 := by rw [e1s]; unfold bor; split <;> omega
  obtain ⟨e2s, e2v⟩ := step a2 (UInt256.shiftRight t1 (UInt256.ofNat 255)) n2 (by omega) (by omega) hb1
  rw [← ht2] at e2s e2v
  have hb2 : (UInt256.shiftRight t2 (UInt256.ofNat 255)).toNat ≤ 1 := by rw [e2s]; unfold bor; split <;> omega
  obtain ⟨e3s, e3v⟩ := step a3 (UInt256.shiftRight t2 (UInt256.ofNat 255)) n3 (by omega) (by omega) hb2
  rw [← ht3] at e3s e3v
  have hb3 : (UInt256.shiftRight t3 (UInt256.ofNat 255)).toNat ≤ 1 := by rw [e3s]; unfold bor; split <;> omega
  obtain ⟨e4s, e4v⟩ := step a4 (UInt256.shiftRight t3 (UInt256.ofNat 255)) n4 (by omega) (by omega) hb3
  rw [← ht4] at e4s e4v
  generalize hs0 : (UInt256.shiftRight t0 (UInt256.ofNat 255)).toNat = s0 at *
  generalize hs1 : (UInt256.shiftRight t1 (UInt256.ofNat 255)).toNat = s1 at *
  generalize hs2 : (UInt256.shiftRight t2 (UInt256.ofNat 255)).toNat = s2 at *
  generalize hs3 : (UInt256.shiftRight t3 (UInt256.ofNat 255)).toNat = s3 at *
  have d0 := digit t0.toNat a0.toNat n0.toNat 0 s0 (by rw [e0s]; omega) hb0 t0.val.isLt ha0 hn0 (by omega)
  have d1 := digit t1.toNat a1.toNat n1.toNat s0 s1 (by rw [e1s]; exact e1v) hb1 t1.val.isLt ha1 hn1 hb0
  have d2 := digit t2.toNat a2.toNat n2.toNat s1 s2 (by rw [e2s]; exact e2v) hb2 t2.val.isLt ha2 hn2 hb1
  have d3 := digit t3.toNat a3.toNat n3.toNat s2 s3 (by rw [e3s]; exact e3v) hb3 t3.val.isLt ha3 hn3 hb2
  have r0 : t0.toNat % 2^240 < 2^240 := Nat.mod_lt _ (by norm_num)
  have r1 : t1.toNat % 2^240 < 2^240 := Nat.mod_lt _ (by norm_num)
  have r2 : t2.toNat % 2^240 < 2^240 := Nat.mod_lt _ (by norm_num)
  have r3 : t3.toNat % 2^240 < 2^240 := Nat.mod_lt _ (by norm_num)
  have ht4 : t4.toNat < 2^256 := t4.val.isLt
  rw [land_M_toNat t0, land_M_toNat t1, land_M_toNat t2, land_M_toNat t3]
  unfold bor at e4s e4v
  by_cases h : n4.toNat + s3 ≤ a4.toNat
  · rw [if_pos h] at e4s e4v
    rw [e4s, if_pos (by omega)]
    exact ⟨rfl, fun _ => ⟨by omega, r0, r1, r2, r3, by omega⟩⟩
  · rw [if_neg h] at e4s e4v
    rw [e4s, if_neg (by omega)]
    exact ⟨rfl, fun h' => absurd h' (by omega)⟩

end CycleSubmission.R5.NormMath
