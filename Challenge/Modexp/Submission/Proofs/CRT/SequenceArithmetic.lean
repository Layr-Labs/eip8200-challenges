import Challenge.Modexp.Submission.Proofs.CRT.ColumnSequence
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace HistoricalSearch.SequenceArithmetic
open EvmSemantics EvmSemantics.EVM
open HistoricalSearch.GeneratedArithmetic HistoricalSearch.ColumnMemory
open HistoricalSearch.ColumnSequence HistoricalSearch.MixedMontgomery

variable (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)

def finalQ (i : Nat) : UInt256 := qRead (states s minv n rest 17).memory i
def finalD (t : Nat) : Nat := if t < 8 then 0 else (dRead (states s minv n rest 17).memory (t-8)).toNat
def localSum (t : Nat) : Nat := UniformColumns.sum t (incoming s minv n rest t) minv
  (aRead (states s minv n rest t).memory) n (qRead (states s minv n rest t).memory)

theorem q_bounds (i : Nat) (hi : i < 9) : (finalQ s minv n rest i).toNat < radix := by
  unfold finalQ
  rw [q_set s minv n rest i hi]
  exact UniformColumns.cancelRange i hi _ _ _ _ _

theorem q_top : (finalQ s minv n rest 8).toNat < 2^96 := by
  unfold finalQ
  rw [q_set s minv n rest 8 (by decide)]
  exact UniformColumns.cancelTop _ _ _ _ _

theorem prior_q (t i : Nat) (ht : t ≤ 17) (hi : i < 9) (hit : i < t) :
    qRead (states s minv n rest t).memory i = finalQ s minv n rest i := by
  exact (q_preserved s minv n rest t 17 ht (by decide) i hi hit).symm

theorem carry_bound
    (ha : ∀ i < 9, (aRead s.memory i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0) (t : Nat) (ht : t ≤ 16) :
    (incoming s minv n rest t).toNat ≤ 18*(radix-1) := by
  induction t with
  | zero => simp [incoming, UInt256.ofNat, UInt256.toNat]
  | succ t ih =>
    rw [next_carry s minv n rest t (by omega)]
    apply UniformColumns.carryBound t (by omega) (N := N)
    · intro j hj
      rw [a_preserved s minv n rest t (by omega) j hj]
      exact ha j hj
    · exact hn
    · intro j hj
      rw [prior_q s minv n rest t j (by omega) (by omega) (by omega)]
      exact q_bounds s minv n rest j (by omega)
    · exact ih (by omega)
    · exact hn0
    · exact hinv

theorem carry_value
    (ha : ∀ i < 9, (aRead s.memory i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0) (t : Nat) (ht : t < 16) :
    (incoming s minv n rest (t+1)).toNat = localSum s minv n rest t / radix := by
  rw [next_carry s minv n rest t ht]
  apply UniformColumns.carry t ht (N := N)
  · intro j hj
    rw [a_preserved s minv n rest t (by omega) j hj]
    exact ha j hj
  · exact hn
  · intro j hj
    rw [prior_q s minv n rest t j (by omega) (by omega) (by omega)]
    exact q_bounds s minv n rest j (by omega)
  · exact carry_bound s minv n rest ha hn N hn0 hinv t (by omega)
  · exact hn0
  · exact hinv

theorem carry_top
    (ha : ∀ i < 9, (aRead s.memory i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0)
    (ha8 : (aRead s.memory 8).toNat < 2^96) (hn8 : (n 8).toNat < 2^96) :
    (incoming s minv n rest 16).toNat ≤ 4*((2^96 : Nat)-1)+18 := by
  have he := carry_value s minv n rest ha hn N hn0 hinv 15 (by decide)
  rw [he]
  apply TailArithmetic.col15_sharp
  · rw [a_preserved s minv n rest 15 (by decide) 7 (by decide)]; exact ha 7 (by decide)
  · rw [a_preserved s minv n rest 15 (by decide) 8 (by decide)]; exact ha8
  · exact hn 7 (by decide)
  · exact hn8
  · simp only [ConcreteArithmetic.col15Qs]
    rw [prior_q s minv n rest 15 7 (by decide) (by decide) (by decide)]; exact q_bounds s minv n rest 7 (by decide)
  · simp only [ConcreteArithmetic.col15Qs]
    rw [prior_q s minv n rest 15 8 (by decide) (by decide) (by decide)]; exact q_top s minv n rest
  · exact carry_bound s minv n rest ha hn N hn0 hinv 15 (by decide)

theorem qs_final (t : Nat) (ht : t < 16) (i : Nat) (hi : i < 9) (hit : i ≤ t) :
    UniformColumns.qs t (incoming s minv n rest t) minv
      (aRead (states s minv n rest t).memory) n (qRead (states s minv n rest t).memory) i =
        finalQ s minv n rest i := by
  by_cases ht9 : t < 9
  · rw [UniformColumns.qsPrefix t ht9]
    by_cases he : i = t
    · subst i
      simp only [↓reduceIte]
      exact (q_set s minv n rest t ht9).symm
    · simp only [if_neg he, if_pos (show i < t by omega)]
      exact prior_q s minv n rest t i (by omega) hi (by omega)
  · rw [UniformColumns.qsAfter t (by omega)]
    exact prior_q s minv n rest t i (by omega) hi (by omega)

theorem convolution_congr (k t : Nat) (a b a' b' : Nat → Nat)
    (ha : ∀ i < k, a i = a' i) (hb : ∀ i < k, b i = b' i) :
    convolution k a b t = convolution k a' b' t := by
  unfold convolution
  apply Finset.sum_congr rfl
  intro ij hij
  have hh := Finset.mem_filter.mp hij
  have hi := Finset.mem_product.mp hh.1
  rw [ha ij.1 (Finset.mem_range.mp hi.1), hb ij.2 (Finset.mem_range.mp hi.2)]

theorem sum_convolution (t : Nat) (ht : t < 16) :
    localSum s minv n rest t =
      convolution 9 (fun i => (aRead s.memory i).toNat) (fun i => (aRead s.memory i).toNat) t +
      convolution 9 (fun i => (finalQ s minv n rest i).toNat) (fun i => (n i).toNat) t +
      (incoming s minv n rest t).toNat := by
  unfold localSum
  rw [UniformColumns.sumConvolution t ht]
  have hA : ∀ i < 9, (aRead (states s minv n rest t).memory i).toNat = (aRead s.memory i).toNat := by
    intro i hi; rw [a_preserved s minv n rest t (by omega) i hi]
  rw [convolution_congr 9 t _ _ _ _ hA hA]
  rw [SeventeenColumns.convolution_prefix 9 t _ (fun i => (finalQ s minv n rest i).toNat) _
    (fun i hi hit => congrArg UInt256.toNat (qs_final s minv n rest t ht i hi hit))]
  by_cases he : t = 0
  · subst t
    simp [incoming, UInt256.ofNat, UInt256.toNat]
  · rw [if_neg he]
    omega

#print axioms q_bounds
#print axioms q_top
#print axioms carry_bound
#print axioms carry_top
#print axioms sum_convolution
end HistoricalSearch.SequenceArithmetic
