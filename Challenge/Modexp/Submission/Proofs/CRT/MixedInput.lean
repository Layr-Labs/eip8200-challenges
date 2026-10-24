import Challenge.Modexp.Submission.Proofs.CRT.KernelArithmetic
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.MixedInput
open EvmSemantics
open HistoricalSearch.GeneratedArithmetic HistoricalSearch.MixedMontgomery

theorem value (A : Nat) (a : Nat → UInt256) (hA : A < 2^2048)
    (hlo : ∀ i < 8, (a i).toNat = A / 2^(244*i) % 2^244)
    (hhi : (a 8).toNat = A / 2^1952) :
    weighted radix 9 (fun i => (a i).toNat) = A ∧
    (∀ i < 9, (a i).toNat < radix) ∧ (a 8).toNat < 2^96 := by
  have hpow : (2^1952 : Nat) = radix^8 := by norm_num [radix]
  have hp : 0 < radix^8 := Nat.pow_pos (Nat.two_pow_pos 244)
  have htop : (a 8).toNat < 2^96 := by
    rw [hhi, hpow]
    apply (Nat.div_lt_iff_lt_mul hp).2
    have hr := (widthParameters 244 96 (by decide) (by decide)).2
    change (2^2048 : Nat) = radix^8*2^96 at hr
    nlinarith
  have hsmall : (2^96 : Nat) ≤ radix := Nat.pow_le_pow_right (by decide) (by decide)
  have hall : ∀ i < 9, (a i).toNat = A/radix^i % radix := by
    intro i hi
    by_cases hi8 : i < 8
    · rw [hlo i hi8]
      simp [radix, Nat.pow_mul]
    · have he : i = 8 := by omega
      subst i
      rw [hhi, hpow, Nat.mod_eq_of_lt]
      simpa only [hhi, hpow] using htop.trans_le hsmall
  have hbounds : ∀ i < 9, (a i).toNat < radix := by
    intro i hi
    rw [hall i hi]
    exact Nat.mod_lt _ (Nat.two_pow_pos 244)
  have hArad : A < radix^9 := by
    have hr := (widthParameters 244 96 (by decide) (by decide)).2
    change (2^2048 : Nat) = radix^8*2^96 at hr
    have hm := Nat.mul_le_mul_left (radix^8) hsmall
    exact hA.trans_le (by rw [hr, Nat.pow_succ]; exact hm)
  refine ⟨?_, hbounds, htop⟩
  rw [← extractedWordsExact radix 9 A hArad]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [hall i (Finset.mem_range.mp hi)]

#print axioms value
end HistoricalSearch.MixedInput
