import Challenge.Modexp.Submission.Proofs.CRT.CRTLoopArithmetic
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-!
# Digit-wise subtraction on the mixed radix

The overflow handler subtracts the modulus from the retained column value one 244-bit
digit at a time, taking each borrow from bit 255 of the 256-bit difference word.
`sub_step` is that word-level step; `sub_digits` telescopes the borrows with
`carryTelescopes` and reads the digits of the difference back.
-/

namespace HistoricalSearch.OverflowHandlerArith
open EvmSemantics
open Challenge.EvmProof.Word
open HistoricalSearch.MixedMontgomery HistoricalSearch.CRTPacking
open scoped BigOperators

abbrev B : Nat := 2^244

theorem mask_toNat : (UInt256.ofNat (2^244-1)).toNat = 2^244-1 := by
  rw [word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)]

theorem land_mask_toNat (t : UInt256) :
    (UInt256.land (UInt256.ofNat (2^244-1)) t).toNat = t.toNat % 2^244 := by
  rw [HistoricalSearch.CRTAdapterMeaning.land_comm, word_toNat_land, mask_toNat,
    Nat.and_two_pow_sub_one_eq_mod]

theorem signBit_toNat (t : UInt256) :
    (UInt256.shiftRight t (UInt256.ofNat 255)).toNat = t.toNat / 2^255 := by
  rw [shiftRight_toNat _ (by decide : 255 < 256), Nat.shiftRight_eq_div_pow]

/-- `t = d - s` with `d < B` and `s ≤ B`: the sign bit is the borrow and the low
244 bits are the digit of the difference. -/
theorem sub_step (d s : UInt256) (hd : d.toNat < B) (hs : s.toNat ≤ B) :
    (UInt256.shiftRight (d - s) (UInt256.ofNat 255)).toNat = (if d.toNat < s.toNat then 1 else 0) ∧
    (UInt256.land (UInt256.ofNat (2^244-1)) (d - s)).toNat + s.toNat =
      d.toNat + B * (if d.toNat < s.toNat then 1 else 0) := by
  rw [signBit_toNat, land_mask_toNat, word_toNat_sub_cond]
  have hB : B = 2^244 := rfl
  have h256 : (2:Nat)^256 = 2^244 * 2^12 := by norm_num
  have h255 : (2:Nat)^255 = 2^244 * 2^11 := by norm_num
  have hBpos : 0 < (2:Nat)^244 := by positivity
  rw [hB] at hd hs ⊢
  split_ifs with h
  · -- wrapped: t = 2^256 + d - s, in [2^256 - 2^244, 2^256)
    have hdiv : (2^256 + d.toNat - s.toNat) / 2^255 = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have hmod : (2^256 + d.toNat - s.toNat) % 2^244 = 2^244 + d.toNat - s.toNat := by
      have he : 2^256 + d.toNat - s.toNat = (2^244 + d.toNat - s.toNat) + 2^244 * (2^12 - 1) := by omega
      rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hdiv, hmod]
    constructor
    · rfl
    · omega
  · have hlt : d.toNat - s.toNat < 2^244 := by omega
    rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt hlt]
    constructor
    · rfl
    · omega

/-- The top digit: no borrow can be produced when the difference is nonnegative. -/
theorem top_step (d s : UInt256) (h : s.toNat ≤ d.toNat) : (d - s).toNat = d.toNat - s.toNat := by
  rw [word_toNat_sub_cond, if_neg (by omega)]

theorem add_small (n c : UInt256) (hn : n.toNat < B) (hc : c.toNat ≤ 1) :
    (n + c).toNat = n.toNat + c.toNat := by
  rw [word_toNat_add, Nat.mod_eq_of_lt]
  have : (B : Nat) < 2^256 := by norm_num [B]
  omega

theorem weighted_add (n : Nat) (f g : Nat → Nat) :
    weighted B n (fun i => f i + g i) = weighted B n f + weighted B n g := by
  simp only [weighted, Nat.add_mul, Finset.sum_add_distrib]

/-- The low digits of a value reassemble its residue modulo `B^8`. -/
theorem low_weighted (X : Nat) :
    weighted B 8 (fun i => X / B^i % B) = X % B^8 := by
  have hX : X % B^8 < B^8 := Nat.mod_lt _ (by positivity)
  have he := extractedWordsExact B 8 (X % B^8) hX
  rw [← he]
  apply Finset.sum_congr rfl
  intro i hi
  have hi8 := Finset.mem_range.mp hi
  show X / B^i % B * B^i = X % B^8 / B^i % B * B^i
  have hsplit : B^8 = B^i * B^(8-i) := by rw [← Nat.pow_add]; congr 1; omega
  rw [hsplit, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self B (by omega : 8 - i ≠ 0))]

/-- Digits of a weighted sum with digits below the radix. -/
theorem weighted_digit (d : Nat → Nat) (m i : Nat) (hi : i < m) (hd : ∀ j < m, d j < B) :
    weighted B m d / B^i % B = d i := by
  rw [weighted_div B m i d (by positivity) (by omega) hd]
  have hm : m - i = (m - i - 1) + 1 := by omega
  rw [hm, weightedHead, Nat.add_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd i hi)]

theorem sub_digits (Q N T : Nat) (q n r c : Nat → Nat)
    (hq : ∀ i < 8, q i = Q / B^i % B) (hT : T = Q / B^8)
    (hn : ∀ i < 8, n i = N / B^i % B) (hn8 : n 8 = N / B^8)
    (hc0 : c 0 = 0) (hstep : ∀ i < 8, q i + B * c (i+1) = r i + n i + c i)
    (hr : ∀ i < 8, r i < B) (hNQ : N ≤ Q) (hX : Q - N < 2^2048) :
    n 8 + c 8 ≤ T ∧ (∀ i < 8, (Q - N) / B^i % B = r i) ∧ (Q - N) / B^8 = T - n 8 - c 8 := by
  have htel := carryTelescopes B 8 (fun i => r i + n i) q c hc0 (fun i hi => hstep i hi)
  rw [weighted_add] at htel
  have hWQ : weighted B 8 q = Q % B^8 := by
    rw [← low_weighted Q]
    apply Finset.sum_congr rfl
    intro i hi
    show q i * B^i = Q / B^i % B * B^i
    rw [hq i (Finset.mem_range.mp hi)]
  have hWN : weighted B 8 n = N % B^8 := by
    rw [← low_weighted N]
    apply Finset.sum_congr rfl
    intro i hi
    show n i * B^i = N / B^i % B * B^i
    rw [hn i (Finset.mem_range.mp hi)]
  have hWR : weighted B 8 r < B^8 := weighted_lt B 8 r (by positivity) hr
  have hQd := Nat.mod_add_div Q (B^8)
  have hNd := Nat.mod_add_div N (B^8)
  rw [← hWQ, ← hT] at hQd
  rw [← hWN, ← hn8] at hNd
  have hB8 : (B:Nat)^8 = 2^1952 := by norm_num [B]
  rw [hB8] at htel hWR hQd hNd
  have h2048 : (2:Nat)^2048 = 2^1952 * 2^96 := by norm_num
  have hle : n 8 + c 8 ≤ T := by omega
  have hXe : Q - N = weighted B 8 r + 2^1952 * (T - n 8 - c 8) := by omega
  have htop : T - n 8 - c 8 < 2^96 := by omega
  refine ⟨hle, ?_, ?_⟩
  · intro i hi
    let r' : Nat → Nat := fun j => if j < 8 then r j else T - n 8 - c 8
    have hr' : ∀ j < 9, r' j < B := by
      intro j hj
      by_cases hj8 : j < 8
      · simp only [r', if_pos hj8]; exact hr j hj8
      · simp only [r', if_neg hj8]; exact lt_of_lt_of_le htop (by norm_num [B])
    have hlow : weighted B 8 r' = weighted B 8 r := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [r', if_pos (Finset.mem_range.mp hj)]
    have hhigh : weighted B 1 (fun j => r' (8+j)) = T - n 8 - c 8 := by
      simp [weighted, r']
    have hw : weighted B 9 r' = Q - N := by
      rw [show 9 = 8 + 1 from rfl, weighted_split B 8 1 r', hlow, hhigh, hB8, hXe]
    rw [← hw, weighted_digit r' 9 i (by omega) hr']
    simp only [r', if_pos hi]
  · rw [hXe, hB8.symm, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by rw [hB8]; exact hWR)]
    omega

#print axioms sub_step
#print axioms top_step
#print axioms sub_digits
end HistoricalSearch.OverflowHandlerArith
