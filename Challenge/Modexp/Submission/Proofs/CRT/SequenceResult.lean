import Challenge.Modexp.Submission.Proofs.CRT.SequenceArithmetic
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace HistoricalSearch.SequenceResult
open EvmSemantics EvmSemantics.EVM
open HistoricalSearch.GeneratedArithmetic HistoricalSearch.ColumnMemory
open HistoricalSearch.ColumnSequence HistoricalSearch.MixedMontgomery
open HistoricalSearch.SequenceArithmetic

variable (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)

 theorem digit_value (N : Nat)
    (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0)
    (t : Nat) (ht : t < 16) :
    finalD s minv n rest t = localSum s minv n rest t % radix := by
  by_cases ht8 : t < 8
  · have hc := UniformColumns.cancelled t ht8 (incoming s minv n rest t) minv
      (aRead (states s minv n rest t).memory) n (qRead (states s minv n rest t).memory) N hn0 hinv
    simpa only [finalD, if_pos ht8, localSum] using hc.symm
  · unfold finalD
    rw [if_neg ht8, d_set s minv n rest t (by omega) (by omega)]
    exact UniformColumns.digit t ht (by omega) _ _ _ _ _

 theorem recurrence (N : Nat)
    (ha : ∀ i < 9, (aRead s.memory i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0)
    (t : Nat) (ht : t < 16) :
    finalD s minv n rest t + radix*(incoming s minv n rest (t+1)).toNat =
      convolution 9 (fun i => (aRead s.memory i).toNat) (fun i => (aRead s.memory i).toNat) t +
      convolution 9 (fun i => (finalQ s minv n rest i).toNat) (fun i => (n i).toNat) t +
      (incoming s minv n rest t).toNat := by
  rw [digit_value s minv n rest N hn0 hinv t ht, carry_value s minv n rest ha hn N hn0 hinv t ht,
    Nat.mod_add_div]
  exact sum_convolution s minv n rest t ht

 theorem top_value
    (ha : ∀ i < 9, (aRead s.memory i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0)
    (ha8 : (aRead s.memory 8).toNat < 2^96) (hn8 : (n 8).toNat < 2^96) :
    finalD s minv n rest 16 = (aRead s.memory 8).toNat*(aRead s.memory 8).toNat +
      (finalQ s minv n rest 8).toNat*(n 8).toNat+(incoming s minv n rest 16).toNat ∧
    finalD s minv n rest 16 < radix := by
  have haa : (aRead (states s minv n rest 16).memory 8).toNat < 2^96 := by
    rw [a_preserved s minv n rest 16 (by decide) 8 (by decide)]; exact ha8
  have hqq : (qRead (states s minv n rest 16).memory 8).toNat < 2^96 := by
    rw [prior_q s minv n rest 16 8 (by decide) (by decide) (by decide)]; exact q_top s minv n rest
  have hv := ColumnContracts.col16_digit (incoming s minv n rest 16) minv
    (aRead (states s minv n rest 16).memory) n (qRead (states s minv n rest 16).memory)
    haa hn8 hqq (carry_top s minv n rest ha hn N hn0 hinv ha8 hn8)
  change (outWords s minv n rest 16).digit.toNat = _ ∧
    (outWords s minv n rest 16).digit.toNat < radix at hv
  rw [a_preserved s minv n rest 16 (by decide) 8 (by decide),
    prior_q s minv n rest 16 8 (by decide) (by decide) (by decide)] at hv
  simpa only [finalD, show ¬(16 < 8) from by decide, ↓reduceIte,
    d_set s minv n rest 16 (by decide) (by decide)] using hv

 theorem tail
    (ha : ∀ i < 9, (aRead s.memory i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0)
    (ha8 : (aRead s.memory 8).toNat < 2^96) (hn8 : (n 8).toNat < 2^96) :
    finalD s minv n rest 16 =
      convolution 9 (fun i => (aRead s.memory i).toNat) (fun i => (aRead s.memory i).toNat) 16 +
      convolution 9 (fun i => (finalQ s minv n rest i).toNat) (fun i => (n i).toNat) 16 +
      (incoming s minv n rest 16).toNat := by
  rw [(top_value s minv n rest ha hn N hn0 hinv ha8 hn8).1]
  simp [convolution, Finset.sum_filter, Finset.sum_product, Finset.sum_range_succ]

 theorem output_digits
    (ha : ∀ i < 9, (aRead s.memory i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0)
    (ha8 : (aRead s.memory 8).toNat < 2^96) (hn8 : (n 8).toNat < 2^96)
    (i : Nat) (hi : i < 9) :
    (dRead (states s minv n rest 17).memory i).toNat < radix := by
  by_cases hi8 : i < 8
  · have hd := d_set s minv n rest (8+i) (by omega) (by omega)
    have hv := UniformColumns.digit (8+i) (by omega) (by omega)
      (incoming s minv n rest (8+i)) minv (aRead (states s minv n rest (8+i)).memory)
      n (qRead (states s minv n rest (8+i)).memory)
    simp only [Nat.add_sub_cancel_left] at hd
    rw [hd]
    change (words (8+i) _ _ _ _ _).digit.toNat < radix
    rw [hv]
    exact Nat.mod_lt _ (Nat.two_pow_pos 244)
  · have he : i = 8 := by omega
    subst i
    exact (top_value s minv n rest ha hn N hn0 hinv ha8 hn8).2

 theorem high_cancelled (N : Nat)
    (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    finalD s minv n rest 8 % 2^96 = 0 := by
  rw [digit_value s minv n rest N hn0 hinv 8 (by decide)]
  change (localSum s minv n rest 8 % 2^244) % 2^96 = 0
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 96 ≤ 244))]
  exact UniformColumns.cancelledTop _ _ _ _ _ N hn0 hinv

def output : Nat := weighted radix 9 (fun i => (dRead (states s minv n rest 17).memory i).toNat) / 2^96

 theorem output_eq :
    output s minv n rest = weighted radix 9 (fun i => finalD s minv n rest (8+i)) / 2^96 := by
  simp [output, finalD]

 theorem exact_output (N : Nat)
    (ha : ∀ i < 9, (aRead s.memory i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (ha8 : (aRead s.memory 8).toNat < 2^96) (hn8 : (n 8).toNat < 2^96)
    (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    output s minv n rest * 2^2048 =
      weighted radix 9 (fun i => (aRead s.memory i).toNat) ^ 2 +
      weighted radix 9 (fun i => (finalQ s minv n rest i).toNat) * weighted radix 9 (fun i => (n i).toNat) := by
  rw [output_eq, pow_two]
  apply SeventeenColumns.exact17 radix (2^96) (2^2048) _ _ _ _ (fun t => (incoming s minv n rest t).toNat)
  · exact Nat.pow_dvd_pow 2 (by decide)
  · exact (widthParameters 244 96 (by decide) (by decide)).2
  · simp [incoming, UInt256.ofNat, UInt256.toNat]
  · intro i hi; simp [finalD, hi]
  · exact high_cancelled s minv n rest N hn0 hinv
  · exact recurrence s minv n rest N ha hn hn0 hinv
  · exact tail s minv n rest ha hn N hn0 hinv ha8 hn8

#print axioms recurrence
#print axioms tail
#print axioms output_digits
#print axioms exact_output
end HistoricalSearch.SequenceResult
