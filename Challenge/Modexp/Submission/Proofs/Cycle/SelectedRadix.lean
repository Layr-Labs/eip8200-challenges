import Challenge.Modexp.Submission.Proofs.CRT.MixedMontgomery
import Challenge.Modexp.Submission.Proofs.CRT.CancelledCRT
import Challenge.Modexp.Submission.Proofs.CRT.RoundedCRT

set_option warningAsError true
set_option maxHeartbeats 3000000
set_option exponentiation.threshold 4096

namespace CycleSubmission.Radix
open HistoricalSearch.MixedMontgomery
open Challenge.Modexp.Submission.Proofs.Fast.Model

theorem rescaleEntry (R S N A x : Nat) (hS : 0 < S) (hA : A < R)
    (hform : A ≡ x*R [MOD N]) :
    A*S < R*S ∧ A*S ≡ x*(R*S) [MOD N] := by
  refine ⟨Nat.mul_lt_mul_of_pos_right hA hS, ?_⟩
  simpa only [Nat.mul_assoc] using hform.mul_right S

theorem alignedExact (beta : Nat) (a b q m d c : Nat → Nat)
    (hc : c 0 = 0) (hfinal : c 18 = 0)
    (hzero : ∀ i < 9, d i = 0)
    (hrec : ∀ i < 18, d i + beta*c (i+1) =
      convolution 9 a b i + convolution 9 q m i + c i) :
    weighted beta 9 (fun i => d (9+i)) * beta^9 =
      weighted beta 9 a * weighted beta 9 b +
        weighted beta 9 q * weighted beta 9 m := by
  have h := montgomeryColumns beta 9 a b q m d c hc hrec
  have hs := weightedShift beta 9 9 d hzero
  change weighted beta 18 d = _ at hs
  change weighted beta 18 d + beta^18*c 18 = _ at h
  rw [hfinal, Nat.mul_zero, Nat.add_zero, hs] at h
  simpa only [Nat.mul_comm] using h

theorem alignedContract (beta : Nat) (a b q m d c : Nat → Nat)
    (hbeta : 0 < beta) (hc : c 0 = 0) (hfinal : c 18 = 0)
    (hzero : ∀ i < 9, d i = 0)
    (hrec : ∀ i < 18, d i + beta*c (i+1) =
      convolution 9 a b i + convolution 9 q m i + c i)
    (hq : ∀ i < 9, q i < beta)
    (hA : weighted beta 9 a < beta^9)
    (hB : weighted beta 9 b < beta^9)
    (hN : 0 < weighted beta 9 m) (hNR : weighted beta 9 m < beta^9)
    (hcop : Nat.Coprime (beta^9) (weighted beta 9 m)) :
    normalize (beta^9) (weighted beta 9 m) (weighted beta 9 (fun i => d (9+i))) < beta^9 ∧
    normalize (beta^9) (weighted beta 9 m) (weighted beta 9 (fun i => d (9+i))) % weighted beta 9 m =
      montMul (weighted beta 9 m) (beta^9) (weighted beta 9 a) (weighted beta 9 b) := by
  apply arithmeticContract _ _ _ _ _ _ (Nat.pow_pos hbeta) hN hNR hA hB
    (weightedBound beta 9 q hbeta hq) hcop
  exact alignedExact beta a b q m d c hc hfinal hzero hrec

theorem overflowTest (beta lo top : Nat) (hbeta : 0 < beta)
    (hlo : lo < beta^8) :
    beta^9 ≤ lo+beta^8*top ↔ beta ≤ top := by
  have hp : 0 < beta^8 := Nat.pow_pos hbeta
  rw [Nat.pow_succ]
  constructor
  · intro h
    by_contra hn
    have : top+1 ≤ beta := by omega
    nlinarith
  · intro h
    nlinarith

theorem squareStep (R N A Q T : Nat)
    (hR : 0 < R) (hN : 0 < N) (hNR : N < R)
    (hA : A < R) (hQ : Q < R) (hcop : Nat.Coprime R N)
    (hexact : T*R = A*A + Q*N) :
    normalize R N T < R ∧ normalize R N T % N = montMul N R A A :=
  arithmeticContract R N A A Q T hR hN hNR hA hA hQ hcop hexact

theorem squareChainRange (R N : Nat) (a q t : Nat → Nat)
    (hR : 0 < R) (hN : 0 < N) (hNR : N < R)
    (hstart : a 0 < R) (hq : ∀ i, q i < R)
    (hexact : ∀ i, t i*R = a i*a i + q i*N)
    (hnext : ∀ i, a (i+1) = normalize R N (t i)) : ∀ i, a i < R := by
  intro i
  induction i with
  | zero => exact hstart
  | succ i ih =>
    rw [hnext i]
    apply (normalizeCorrect R N (t i) hNR ?_).1
    have ht : t i = (a i*a i+q i*N)/R := by
      rw [← hexact i, Nat.mul_div_cancel _ hR]
    rw [ht]
    exact montgomeryRange R N (a i) (a i) (q i) hR hN ih ih (hq i)

theorem squareForm (R N A Q T x : Nat)
    (hR : 0 < R) (hN : 0 < N) (hNR : N < R)
    (hA : A < R) (hQ : Q < R) (hcop : Nat.Coprime R N)
    (hexact : T*R = A*A+Q*N) (hform : A ≡ x*R [MOD N]) :
    normalize R N T ≡ (x*x)*R [MOD N] := by
  change normalize R N T % N = _
  rw [(squareStep R N A Q T hR hN hNR hA hQ hcop hexact).2]
  exact montMul_form hN hcop hform hform

theorem squareChainContract (R N x : Nat) (a q t : Nat → Nat)
    (hR : 0 < R) (hN : 0 < N) (hNR : N < R)
    (hstart : a 0 < R) (hform : a 0 ≡ x*R [MOD N])
    (hq : ∀ i, q i < R) (hcop : Nat.Coprime R N)
    (hexact : ∀ i, t i*R = a i*a i+q i*N)
    (hnext : ∀ i, a (i+1) = normalize R N (t i)) :
    ∀ i, a i < R ∧ a i ≡ x^(2^i)*R [MOD N] := by
  intro i
  have hrange := squareChainRange R N a q t hR hN hNR hstart hq hexact hnext
  refine ⟨hrange i, ?_⟩
  induction i with
  | zero => simpa only [Nat.pow_zero, Nat.pow_one] using hform
  | succ i ih =>
    rw [hnext i]
    have h := squareForm R N (a i) (q i) (t i) (x^(2^i))
      hR hN hNR (hrange i) (hq i) hcop (hexact i) ih
    have he : x^(2^(i+1)) = x^(2^i)*x^(2^i) := by
      rw [Nat.pow_succ, Nat.mul_two, Nat.pow_add]
    rw [he]
    exact h

theorem finalProductRange (R N A B Q T : Nat)
    (hR : 0 < R) (hN : 0 < N) (hA : A < R) (hB : B < N)
    (hQ : Q < R) (hexact : T*R = A*B+Q*N) : T < 2*N := by
  have hab : A*B < R*N := Nat.mul_lt_mul_of_lt_of_lt hA hB
  have hqn : Q*N < R*N := Nat.mul_lt_mul_of_pos_right hQ hN
  apply (Nat.mul_lt_mul_right hR).mp
  nlinarith

theorem canonicalExit (N T : Nat) (hT : T < 2*N) :
    (if N ≤ T then T-N else T) = T % N := by
  split_ifs with h
  · have hlt : T-N < N := by omega
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt hlt]
  · exact (Nat.mod_eq_of_lt (by omega)).symm

theorem finalProductContract (R N A B Q T x : Nat)
    (hR : 0 < R) (hN : 0 < N) (hA : A < R) (hB : B < N)
    (hQ : Q < R) (hcop : Nat.Coprime R N)
    (hexact : T*R = A*B+Q*N) (hform : A ≡ x*R [MOD N]) :
    (if N ≤ T then T-N else T) = B*x % N := by
  rw [canonicalExit N T (finalProductRange R N A B Q T hR hN hA hB hQ hexact)]
  have hm := montMul_eq_mod_of_mul_eq hN hcop
    (show T*R = B*A+Q*N by simpa only [Nat.mul_comm] using hexact)
  rw [← hm]
  exact montMul_const_form hN hcop hform B

theorem overwriteAfterLastRead (i j : Nat) (hj : j < 9) :
    i+j < 9+i ∧ j+i < 9+i := by omega

theorem selectedParameters (N : Nat) (hN : N < 2^2048) :
    (2^240 : Nat)^9 = 2^2048 * 2^112 ∧ N < (2^240)^9 := by
  norm_num at hN ⊢
  omega

theorem oddCoprime (W N : Nat) (hodd : Odd N) :
    Nat.Coprime ((2^W)^9) N := by
  exact (Nat.Coprime.pow_left W (Nat.coprime_two_left.mpr hodd)).pow_left 9

end CycleSubmission.Radix

set_option warningAsError true
set_option maxHeartbeats 2000000
namespace CycleSubmission.Bounds
open HistoricalSearch.CRTColumn

theorem fullColumnBounds (S C : Nat)
    (hC : C ≤ 18*((2^240 : Nat)-1))
    (hS : S ≤ 18*((2^240 : Nat)-1)^2+C) :
    S/2^240 ≤ 18*((2^240 : Nat)-1) ∧
    S/2^240 < residueModulus ∧
    (S/wordRadix+1)*32-1 < residueModulus := by
  have hc := columnCarryBound (2^240) 18 S C (Nat.two_pow_pos _) hC hS
  refine ⟨hc, ?_, HistoricalSearch.RoundedCRT.roundedWidthBound 240 S C (by decide) hC hS⟩
  norm_num [residueModulus] at hc ⊢
  omega

theorem highAccumulatorFits (H : Nat) (hH : H ≤ 19*(residueModulus-1)) :
    H < wordRadix := by
  norm_num [residueModulus, wordRadix] at hH ⊢
  omega

theorem cancelledRecovery (S C H : Nat)
    (hC : C ≤ 18*((2^240 : Nat)-1))
    (hS : S ≤ 18*((2^240 : Nat)-1)^2+C)
    (hH : H%residueModulus = S%residueModulus) (hcancel : S%2^240=0) :
    (H*2048)%residueModulus = S/2^240 := by
  exact HistoricalSearch.CancelledCRT.cancelledResidual (2^240) residueModulus 2048 S H
    (Nat.two_pow_pos _) (by norm_num [residueModulus])
    (by norm_num [residueModulus]) hH hcancel (fullColumnBounds S C hC hS).2.1

theorem roundedRecovery (S C H : Nat)
    (hC : C ≤ 18*((2^240 : Nat)-1))
    (hS : S ≤ 18*((2^240 : Nat)-1)^2+C)
    (hH : H%residueModulus = S%residueModulus) :
    ((H+(wordRadix-1-S%wordRadix))%residueModulus)/32 = S/wordRadix := by
  exact HistoricalSearch.RoundedCRT.roundedHigh wordRadix residueModulus 32 S H
    (by norm_num [wordRadix]) (by norm_num [residueModulus]) (by decide)
    (by norm_num [wordRadix,residueModulus]) hH (fullColumnBounds S C hC hS).2.2

end CycleSubmission.Bounds
namespace CycleSubmission.Bounds
open HistoricalSearch.CRTColumn

theorem selectedCarrySplit (S : Nat) :
    S % (2^256) / (2^240) + S / (2^256) * (2^16) = S / (2^240) := by
  have h := carryFromHigh (2^240) (2^16) S (Nat.two_pow_pos _)
  norm_num at h ⊢
  exact h

theorem selectedCancellationInverse :
    ((2^240 : Nat) * 2048) % (2^251 - 1) = 1 := by norm_num

end CycleSubmission.Bounds
