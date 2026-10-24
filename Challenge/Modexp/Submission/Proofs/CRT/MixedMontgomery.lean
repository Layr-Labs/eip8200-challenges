import Challenge.Modexp.Submission.Proofs.Fast.Model
import Mathlib.Tactic
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.MixedMontgomery

open scoped BigOperators
open Challenge.Modexp.Submission.Proofs.Fast.Model

def weighted (B n : Nat) (f : Nat → Nat) : Nat :=
  ∑ i ∈ Finset.range n, f i * B^i

def convolution (k : Nat) (a b : Nat → Nat) (t : Nat) : Nat :=
  ∑ ij ∈ (Finset.range k ×ˢ Finset.range k).filter (fun ij => ij.1 + ij.2 = t),
    a ij.1 * b ij.2

/-- Regrouping every limb product by its column yields the full product. -/
theorem convolutionValue (B k : Nat) (a b : Nat → Nat) :
    weighted B (2*k) (convolution k a b) = weighted B k a * weighted B k b := by
  have hmap : ∀ ij ∈ Finset.range k ×ˢ Finset.range k,
      ij.1 + ij.2 ∈ Finset.range (2*k) := by
    intro ij hij
    simp only [Finset.mem_product, Finset.mem_range] at hij ⊢
    omega
  unfold weighted convolution
  conv_lhs => simp only [Finset.sum_mul]
  calc
    (∑ t ∈ Finset.range (2*k), ∑ ij ∈
      (Finset.range k ×ˢ Finset.range k).filter (fun ij => ij.1 + ij.2 = t),
      a ij.1 * b ij.2 * B^t)
      = ∑ t ∈ Finset.range (2*k), ∑ ij ∈
        (Finset.range k ×ˢ Finset.range k).filter (fun ij => ij.1 + ij.2 = t),
        a ij.1 * b ij.2 * B^(ij.1+ij.2) := by
          apply Finset.sum_congr rfl
          intro t _
          apply Finset.sum_congr rfl
          intro ij hij
          rw [(Finset.mem_filter.mp hij).2]
    _ = ∑ ij ∈ Finset.range k ×ˢ Finset.range k,
      a ij.1 * b ij.2 * B^(ij.1+ij.2) :=
        Finset.sum_fiberwise_of_maps_to hmap _
    _ = (∑ i ∈ Finset.range k, a i * B^i) * (∑ j ∈ Finset.range k, b j * B^j) := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.pow_add]
      ring

/-- Column carry recurrence telescopes without dropping the final carry. -/
theorem carryTelescopes (B n : Nat) (f d c : Nat → Nat)
    (hc : c 0 = 0)
    (hrec : ∀ i < n, d i + B * c (i+1) = f i + c i) :
    weighted B n d + B^n * c n = weighted B n f := by
  induction n with
  | zero => simp [weighted, hc]
  | succ n ih =>
    have hi := ih (fun i hi => hrec i (by omega))
    have hn := congrArg (fun v => v * B^n) (hrec n (by omega))
    simp only [weighted, Finset.sum_range_succ, Nat.pow_succ] at hi ⊢
    nlinarith

/-- The actual two-convolution column recurrence sums to A*B+Q*N. -/
theorem montgomeryColumns (B k : Nat) (a b q m d c : Nat → Nat)
    (hc : c 0 = 0)
    (hrec : ∀ i < 2*k, d i + B * c (i+1) =
      convolution k a b i + convolution k q m i + c i) :
    weighted B (2*k) d + B^(2*k) * c (2*k) =
      weighted B k a * weighted B k b + weighted B k q * weighted B k m := by
  have ht := carryTelescopes B (2*k)
    (fun i => convolution k a b i + convolution k q m i) d c hc hrec
  have hadd : weighted B (2*k) (fun i => convolution k a b i + convolution k q m i) =
      weighted B (2*k) (convolution k a b) + weighted B (2*k) (convolution k q m) := by
    simp [weighted, Nat.add_mul, Finset.sum_add_distrib]
  rw [hadd, convolutionValue, convolutionValue] at ht
  exact ht

theorem weightedShift (B n k : Nat) (d : Nat → Nat)
    (hzero : ∀ i < n, d i = 0) :
    weighted B (n+k) d = B^n * weighted B k (fun i => d (n+i)) := by
  have hz : (∑ i ∈ Finset.range n, d i * B^i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i (Finset.mem_range.mp hi), Nat.zero_mul]
  simp only [weighted, Finset.sum_range_add, hz, Nat.zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.pow_add]
  ring

theorem weightedHead (B n : Nat) (d : Nat → Nat) :
    weighted B (n+1) d = d 0 + B * weighted B n (fun i => d (i+1)) := by
  simp only [weighted, Finset.sum_range_succ', Nat.pow_zero, Nat.mul_one, Finset.mul_sum]
  rw [Nat.add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.pow_succ]
  ring

/-- The digit chosen with a negative inverse cancels the current low radix. -/
theorem cancellationDigit (r z n np : Nat)
    (hinv : (n*np+1) % r = 0) :
    (z + ((z*np) % r)*n) % r = 0 := by
  have hinv' : (n : ZMod r)*np + 1 = 0 := by
    have hh : n*np+1 ≡ 0 [MOD r] := by simpa only [Nat.ModEq, Nat.zero_mod] using hinv
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).2 hh
  have hmod : (((z*np) % r : Nat) : ZMod r) = (z : ZMod r)*np := by
    simp
  have hz : ((z + ((z*np) % r)*n : Nat) : ZMod r) = 0 := by
    push_cast
    rw [hmod]
    calc (z : ZMod r) + z*np*n = z*(n*np+1) := by ring
      _ = 0 := by rw [hinv', mul_zero]
  have hz' : ((z + ((z*np) % r)*n : Nat) : ZMod r) = ((0 : Nat) : ZMod r) := by
    simpa only [Nat.cast_zero] using hz
  have hh := (ZMod.natCast_eq_natCast_iff _ _ _).1 hz'
  simpa only [Nat.ModEq, Nat.zero_mod] using hh

theorem weightedBound (B n : Nat) (f : Nat → Nat) (hB : 0 < B)
    (hf : ∀ i < n, f i < B) : weighted B n f < B^n := by
  induction n with
  | zero => simp [weighted]
  | succ n ih =>
    have hi := ih (fun i hi => hf i (by omega))
    have hn := hf n (by omega)
    have hp : 0 < B^n := Nat.pow_pos hB
    simp only [weighted, Finset.sum_range_succ, Nat.pow_succ] at hi ⊢
    nlinarith

def highBlock (beta : Nat) (d c : Nat → Nat) : Nat :=
  weighted beta 10 (fun i => d (8+i)) + beta^10 * c 18

/-- Discarding the eight zero limbs retains the exact undivided high block. -/
theorem highBlockExact (beta : Nat) (a b q m d c : Nat → Nat)
    (hc : c 0 = 0) (hzero : ∀ i < 8, d i = 0)
    (hrec : ∀ i < 18, d i + beta * c (i+1) =
      convolution 9 a b i + convolution 9 q m i + c i) :
    beta^8 * highBlock beta d c =
      weighted beta 9 a * weighted beta 9 b + weighted beta 9 q * weighted beta 9 m := by
  have hh := montgomeryColumns beta 9 a b q m d c hc hrec
  have hs := weightedShift beta 8 10 d hzero
  change weighted beta 18 d = _ at hs
  change weighted beta 18 d + beta^18 * c 18 = _ at hh
  rw [hs] at hh
  unfold highBlock
  calc beta^8 * (weighted beta 10 (fun i => d (8+i)) + beta^10*c 18)
      = beta^8 * weighted beta 10 (fun i => d (8+i)) + beta^18*c 18 := by
        rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add]
    _ = _ := hh

/-- The final mixed-width cancellation makes the stored high block exactly
divisible by F. The proof works for any beta and any F dividing beta. -/
theorem mixedExact (beta F R : Nat) (a b q m d c : Nat → Nat)
    (hF : F ∣ beta) (hR : R = beta^8 * F)
    (hc : c 0 = 0) (hzero : ∀ i < 8, d i = 0) (hlast : d 8 % F = 0)
    (hrec : ∀ i < 18, d i + beta * c (i+1) =
      convolution 9 a b i + convolution 9 q m i + c i) :
    (highBlock beta d c / F) * R =
      weighted beta 9 a * weighted beta 9 b + weighted beta 9 q * weighted beta 9 m := by
  have hh := highBlockExact beta a b q m d c hc hzero hrec
  have hs : highBlock beta d c = d 8 + beta *
      (weighted beta 9 (fun i => d (9+i)) + beta^9*c 18) := by
    unfold highBlock
    rw [show 10 = 9+1 from rfl, weightedHead]
    simp only [Nat.add_zero]
    have hfun : (fun i => d (8+(i+1))) = (fun i => d (9+i)) := by
      funext i
      congr 1
      omega
    rw [hfun, Nat.pow_succ]
    ring
  have hd : F ∣ highBlock beta d c := by
    rw [hs]
    apply Nat.dvd_add
    · exact Nat.dvd_of_mod_eq_zero hlast
    · exact dvd_mul_of_dvd_left hF _
  rw [hR]
  calc highBlock beta d c / F * (beta^8 * F)
      = beta^8 * (highBlock beta d c / F * F) := by ring
    _ = beta^8 * highBlock beta d c := by rw [Nat.div_mul_cancel hd]
    _ = _ := hh

/-- Eight radix-beta cancellation digits plus one radix-F digit fit beta^8*F. -/
theorem mixedCancellationBound (beta F : Nat) (q : Nat → Nat) (hbeta : 0 < beta)
    (hlo : ∀ i < 8, q i < beta) (hhi : q 8 < F) :
    weighted beta 9 q < beta^8*F := by
  have hp := weightedBound beta 8 q hbeta hlo
  have hsplit : weighted beta 9 q = weighted beta 8 q + q 8 * beta^8 := by
    simp only [weighted, show 9 = 8+1 from rfl, Finset.sum_range_succ]
  rw [hsplit]
  have hpow : 0 < beta^8 := Nat.pow_pos hbeta
  nlinarith

/-- A single overflow subtraction suffices even when inputs are merely below R,
rather than reduced below the modulus. -/
theorem montgomeryRange (R N A B Q : Nat) (hR : 0 < R)
    (hN : 0 < N) (hA : A < R) (hB : B < R) (hQ : Q < R) :
    (A*B + Q*N) / R < R + N := by
  have hab : A*B < R*R := Nat.mul_lt_mul_of_lt_of_lt hA hB
  have hqn : Q*N < R*N := Nat.mul_lt_mul_of_pos_right hQ hN
  apply (Nat.div_lt_iff_lt_mul hR).2
  nlinarith

def normalize (R N T : Nat) : Nat := if R ≤ T then T-N else T

theorem normalizeCorrect (R N T : Nat) (hN : N < R) (hT : T < R+N) :
    normalize R N T < R ∧ normalize R N T % N = T % N := by
  unfold normalize
  split_ifs with ht
  · have hn : N ≤ T := by omega
    exact ⟨by omega, (Nat.mod_eq_sub_mod hn).symm⟩
  · exact ⟨by omega, rfl⟩

/-- Generic arithmetic contract for plugging the new multiplication into the
existing Montgomery model. Exact divisibility must be supplied by cancellation. -/
theorem arithmeticContract (R N A B Q T : Nat) (hR : 0 < R)
    (hN : 0 < N) (hNR : N < R) (hA : A < R) (hB : B < R) (hQ : Q < R)
    (hcop : Nat.Coprime R N) (hexact : T*R = A*B + Q*N) :
    normalize R N T < R ∧ normalize R N T % N = montMul N R A B := by
  have hT : T = (A*B+Q*N)/R := by rw [← hexact, Nat.mul_div_cancel _ hR]
  have hn := normalizeCorrect R N T hNR
    (by rw [hT]; exact montgomeryRange R N A B Q hR hN hA hB hQ)
  have hm := montMul_eq_mod_of_mul_eq hN hcop hexact
  exact ⟨hn.1, hn.2.trans hm.symm⟩

/-- End-to-end arithmetic model: exact column recurrence and cancellation imply
the existing Montgomery contract, without assuming a product-sum identity. -/
theorem mixedModelContract (beta F R : Nat) (a b q m d c : Nat → Nat)
    (hbeta : 0 < beta) (hFpos : 0 < F) (hF : F ∣ beta) (hR : R = beta^8*F)
    (hc : c 0 = 0) (hzero : ∀ i < 8, d i = 0) (hlast : d 8 % F = 0)
    (hrec : ∀ i < 18, d i + beta * c (i+1) =
      convolution 9 a b i + convolution 9 q m i + c i)
    (hqlow : ∀ i < 8, q i < beta) (hqhigh : q 8 < F)
    (hA : weighted beta 9 a < R) (hB : weighted beta 9 b < R)
    (hN : 0 < weighted beta 9 m) (hNR : weighted beta 9 m < R)
    (hcop : Nat.Coprime R (weighted beta 9 m)) :
    normalize R (weighted beta 9 m) (highBlock beta d c / F) < R ∧
    normalize R (weighted beta 9 m) (highBlock beta d c / F) % weighted beta 9 m =
      montMul (weighted beta 9 m) R (weighted beta 9 a) (weighted beta 9 b) := by
  apply arithmeticContract R (weighted beta 9 m) (weighted beta 9 a)
    (weighted beta 9 b) (weighted beta 9 q) (highBlock beta d c / F)
    (by rw [hR]; exact Nat.mul_pos (Nat.pow_pos hbeta) hFpos) hN hNR hA hB
    (by rw [hR]; exact mixedCancellationBound beta F q hbeta hqlow hqhigh) hcop
  exact mixedExact beta F R a b q m d c hF hR hc hzero hlast hrec

theorem widthParameters (W F : Nat) (heq : 8*W+F = 2048) (hle : F ≤ W) :
    2^F ∣ 2^W ∧ (2^2048 : Nat) = (2^W)^8 * 2^F := by
  refine ⟨Nat.pow_dvd_pow 2 hle, ?_⟩
  rw [← Nat.pow_mul, ← Nat.pow_add]
  congr 1
  omega

theorem oddModulusCoprime (N : Nat) (hodd : Odd N) : Nat.Coprime (2^2048) N :=
  Nat.Coprime.pow_left 2048 (Nat.coprime_two_left.mpr hodd)

/-- Two neighboring digits determine a word-sized window when the remaining
higher digits start at a multiple of the output word radix after shifting. -/
theorem repackArithmetic (B S K W lo hi tail : Nat) (hS : 0 < S)
    (hB : B = S*K) (hW : W ∣ B*K) :
    ((lo + B*hi + B*B*tail) / S) % W = (lo/S + hi*K) % W := by
  have he : lo+B*hi+B*B*tail = lo+(hi*K+B*K*tail)*S := by rw [hB]; ring
  rw [he, Nat.add_mul_div_right _ _ hS]
  have hz : (B*K*tail) % W = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hW _)
  rw [← Nat.add_assoc, Nat.add_mod, hz, Nat.add_zero, Nat.mod_mod]

/-- Exact OR/shift implementation of the two-digit packing formula, including
the EVM left-shift truncation. -/
theorem repackOr (B s k w lo hi tail : Nat)
    (hB : B = 2^s * 2^k) (hW : 2^w ∣ B * 2^k)
    (hlo : lo < B) (hk : k ≤ w) :
    (lo >>> s) ||| ((hi <<< k) % 2^w) =
      ((lo+B*hi+B*B*tail)/2^s) % 2^w := by
  have hs : 0 < 2^s := Nat.two_pow_pos s
  have hl : lo/2^s < 2^k := (Nat.div_lt_iff_lt_mul hs).2 (by simpa [hB, Nat.mul_comm] using hlo)
  have hlw : lo/2^s < 2^w := hl.trans_le (Nat.pow_le_pow_right (by decide) hk)
  rw [repackArithmetic B (2^s) (2^k) (2^w) lo hi tail hs hB hW]
  rw [Nat.add_comm, ← Nat.shiftLeft_eq, ← Nat.shiftRight_eq_div_pow]
  have hshift : lo >>> s < 2^k := by simpa only [Nat.shiftRight_eq_div_pow] using hl
  rw [Nat.shiftLeft_add_eq_or_of_lt hshift, Nat.or_mod_two_pow]
  have hshiftw : lo >>> s < 2^w := by simpa only [Nat.shiftRight_eq_div_pow] using hlw
  rw [Nat.mod_eq_of_lt hshiftw, Nat.or_comm]

/-- Reassembling n extracted words preserves the complete value whenever it
fits n words. This turns the per-window packing equality into an array equality. -/
theorem extractedWordsExact (B n X : Nat) (hX : X < B^n) :
    weighted B n (fun i => X/B^i % B) = X := by
  have hall : ∀ m, weighted B m (fun i => X/B^i % B) + B^m*(X/B^m) = X := by
    intro m
    induction m with
    | zero => simp [weighted]
    | succ m ih =>
      have hh := congrArg (fun v => v*B^m) (Nat.mod_add_div (X/B^m) B)
      have hd : X/B^m/B = X/B^(m+1) := by rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      rw [hd] at hh
      simp only [weighted, Finset.sum_range_succ] at ih ⊢
      simp only [Nat.pow_succ] at hh ⊢
      nlinarith
  have hh := hall n
  rw [Nat.div_eq_of_lt hX, Nat.mul_zero, Nat.add_zero] at hh
  exact hh

theorem repackedWordsExact (w n X : Nat) (words : Nat → Nat) (hX : X < (2^w)^n)
    (hwords : ∀ j < n, words j = X / (2^w)^j % 2^w) :
    weighted (2^w) n words = X := by
  calc
    weighted (2^w) n words = weighted (2^w) n (fun j => X/(2^w)^j % 2^w) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hwords j (Finset.mem_range.mp hj)]
    _ = X := extractedWordsExact (2^w) n X hX


end HistoricalSearch.MixedMontgomery
