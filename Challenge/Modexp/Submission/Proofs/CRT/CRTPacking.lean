import Challenge.Modexp.Submission.Proofs.CRT.MixedMontgomery
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.CRTPacking
open HistoricalSearch.MixedMontgomery
open scoped BigOperators

theorem weighted_lt (B n : Nat) (d : Nat → Nat) (hB : 0 < B)
    (hd : ∀ i < n, d i < B) : weighted B n d < B^n := by
  induction n with
  | zero => simp [weighted]
  | succ n ih =>
    have hn := hd n (by omega)
    have hi := ih (fun i hi => hd i (by omega))
    simp only [weighted, Finset.sum_range_succ, Nat.pow_succ] at hi ⊢
    nlinarith [(show 0 < B^n from Nat.pow_pos hB)]

theorem weighted_split (B lo hi : Nat) (d : Nat → Nat) :
    weighted B (lo+hi) d = weighted B lo d + B^lo * weighted B hi (fun j => d (lo+j)) := by
  simp only [weighted, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.pow_add]
  ring

theorem weighted_div (B n i : Nat) (d : Nat → Nat) (hB : 0 < B) (hi : i ≤ n)
    (hd : ∀ j < n, d j < B) :
    weighted B n d / B^i = weighted B (n-i) (fun j => d (i+j)) := by
  have hl := weighted_lt B i d hB (fun j hj => hd j (by omega))
  have he := weighted_split B i (n-i) d
  rw [Nat.add_sub_of_le hi] at he
  rw [he, Nat.add_mul_div_left _ _ ((show 0 < B^i from Nat.pow_pos hB)), Nat.div_eq_of_lt hl, Nat.zero_add]

theorem weighted_two (B n i : Nat) (d : Nat → Nat) (hB : 0 < B) (hi : i+2 ≤ n)
    (hd : ∀ j < n, d j < B) :
    weighted B n d / B^i = d i + B*d (i+1) +
      B*B*weighted B (n-i-2) (fun j => d (i+2+j)) := by
  rw [weighted_div B n i d hB (by omega) hd]
  have hn : n-i = (n-i-2)+1+1 := by omega
  conv_lhs => rw [hn, weightedHead, weightedHead]
  simp only [Nat.add_zero, Nat.add_assoc]
  ring

/-- A two-digit shift/or window of the stored nine radix244 digits equals a
window of the complete weighted value. -/
theorem two_digit_window (d : Nat → Nat) (i s k w : Nat)
    (hi : i < 8) (hsk : s+k = 244) (hkw : k ≤ w) (hroom : w ≤ 244+k)
    (hd : ∀ j < 9, d j < 2^244) :
    (d i >>> s) ||| ((d (i+1) <<< k) % 2^w) =
      weighted (2^244) 9 d / 2^(244*i+s) % 2^w := by
  have ht := weighted_two (2^244) 9 i d (Nat.two_pow_pos 244) (by omega) hd
  have hp := repackOr (2^244) s k w (d i) (d (i+1))
    (weighted (2^244) (9-i-2) (fun j => d (i+2+j)))
    (by rw [← Nat.pow_add, hsk])
    (by rw [← Nat.pow_add]; exact Nat.pow_dvd_pow 2 hroom)
    (hd i (by omega)) hkw
  rw [← ht] at hp
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_mul, ← Nat.pow_add] at hp
  exact hp

/-- Ordinary256-bit words emitted by the exit adapter recover the low2048
bits of the Montgomery quotient D/2^96. -/
theorem output_word (d : Nat → Nat) (j : Nat) (hj : j < 8)
    (hd : ∀ i < 9, d i < 2^244) :
    (d j >>> (96+12*j)) ||| ((d (j+1) <<< (148-12*j)) % 2^256) =
      (weighted (2^244) 9 d / 2^96) / 2^(256*j) % 2^256 := by
  have hh := two_digit_window d j (96+12*j) (148-12*j) 256 hj
    (by omega) (by omega) (by omega) hd
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  convert hh using 2
  congr 2
  omega

/-- Internal retained rounds produce the same quotient in radix244, without
going through eight ordinary words. -/
theorem retained_digit (d : Nat → Nat) (j : Nat) (hj : j < 8)
    (hd : ∀ i < 9, d i < 2^244) :
    (d j >>> 96) ||| ((d (j+1) <<< 148) % 2^244) =
      (weighted (2^244) 9 d / 2^96) / 2^(244*j) % 2^244 := by
  have hh := two_digit_window d j 96 148 244 hj (by decide) (by decide) (by decide) hd
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  simpa only [Nat.add_comm] using hh

theorem retained_top (d : Nat → Nat) (hd : ∀ i < 9, d i < 2^244) :
    d 8 / 2^96 = (weighted (2^244) 9 d / 2^96) / 2^1952 := by
  have hh := weighted_div (2^244) 9 8 d (Nat.two_pow_pos 244) (by decide) hd
  have ht : weighted (2^244) 9 d / 2^1952 = d 8 := by
    simpa [weighted] using hh
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [← ht, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem quotient_overflow (d : Nat → Nat) (hd : ∀ i < 9, d i < 2^244) :
    d 8 / 2^192 = (weighted (2^244) 9 d / 2^96) / 2^2048 := by
  have hh := weighted_div (2^244) 9 8 d (Nat.two_pow_pos 244) (by decide) hd
  have ht : weighted (2^244) 9 d / 2^1952 = d 8 := by
    simpa [weighted] using hh
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [← ht, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem mod_window (X total shift width : Nat) (h : shift+width ≤ total) :
    (X % 2^total / 2^shift) % 2^width = X/2^shift % 2^width := by
  have hs : shift ≤ total := by omega
  rw [show (2:Nat)^total = 2^shift * 2^(total-shift) by
    rw [← Nat.pow_add, Nat.add_sub_of_le hs], Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))

#print axioms weighted_lt
#print axioms weighted_split
#print axioms weighted_div
#print axioms weighted_two
#print axioms two_digit_window
#print axioms output_word
#print axioms retained_digit
#print axioms retained_top
#print axioms quotient_overflow
#print axioms mod_window
end HistoricalSearch.CRTPacking
