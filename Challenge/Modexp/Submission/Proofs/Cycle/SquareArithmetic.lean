import Challenge.Modexp.Submission.Proofs.Cycle.SquareHistory
import Challenge.Modexp.Submission.Proofs.Cycle.ControlArithmetic
import Challenge.Modexp.Submission.Proofs.Fast.Model
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace CycleSubmission.SquareStep
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open CycleSubmission.WordArithmetic CycleSubmission.WordHistory
open CycleSubmission.ControlArithmetic
open HistoricalSearch.MixedMontgomery

def zeroWords : Nat → UInt256 := fun _ => UInt256.ofNat 0
def digits (inv : UInt256) (a n : Nat → UInt256) : Nat → UInt256 :=
  normalized (squared inv a zeroWords n) n

theorem arithmetic (inv : UInt256) (a n : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix) (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix) (hNvalue : value n = N)
    (hinv : (N*inv.toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hNR : N < radix^9) (hodd : Odd N) :
    (∀ i < 9, (digits inv a n i).toNat < radix) ∧
    value (digits inv a n) < radix^9 ∧
    value (digits inv a n) % N =
      Challenge.Modexp.Submission.Proofs.Fast.Model.montMul N (radix^9) (value a) (value a) := by
  have hz : ∀ i < 9, (zeroWords i).toNat < radix := by
    intro i hi
    exact Nat.two_pow_pos _
  have hlow := (squareTrace inv a zeroWords n).output_low_bound ha hz hn N hn0 hinv
  have hc := (squareTrace inv a zeroWords n).normalized_contract ha hz hn N hn0 hNvalue hinv hN hNR hodd
  have hnr : value n < radix^9 := by rw [hNvalue]; exact hNR
  have hu : value (squared inv a zeroWords n) < radix^9 + value n := by
    rw [hNvalue]
    exact hc.1
  have hd := normalized_bounded (squared inv a zeroWords n) n hlow hn hnr hu
  refine ⟨hd, ?_, ?_⟩
  · rw [digits, normalized_value (squared inv a zeroWords n) n hlow hn hnr, hNvalue]
    exact hc.2.1
  · rw [digits, normalized_value (squared inv a zeroWords n) n hlow hn hnr, hNvalue]
    exact hc.2.2

/-- The Montgomery bound step: `T·R = A² + Q·N` with `Q < R`, `4N ≤ R` and `A + 2N ≤ R`
give `T + 2N ≤ R`. -/
theorem bound_step (A T Q N R : Nat) (he : T * R = A*A + Q*N) (hQ : Q < R)
    (hN4 : 4*N ≤ R) (hb : A + 2*N ≤ R) : T + 2*N ≤ R := by
  have hRpos : 0 < R := by omega
  obtain ⟨A', hA'⟩ : ∃ A', R = A + 2*N + A' := ⟨R - (A + 2*N), by omega⟩
  subst hA'
  have hQ' : Q*N ≤ (A + 2*N + A' - 1)*N := Nat.mul_le_mul_right _ (by omega)
  have hk : 2*N ≤ A + A' := by omega
  have hm : N*(2*N) ≤ N*(A + A') := Nat.mul_le_mul_left _ hk
  have hsub : (A + 2*N + A' - 1)*N + N = (A + 2*N + A')*N := by
    have : 1 ≤ A + 2*N + A' := by omega
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel this]
  have hbig : (T + 2*N) * (A + 2*N + A') ≤ (A + 2*N + A') * (A + 2*N + A') := by
    have h1 : (T + 2*N) * (A + 2*N + A') = A*A + Q*N + 2*N*(A + 2*N + A') := by
      rw [Nat.add_mul, he]
    rw [h1]
    nlinarith [hQ', hm, hsub]
  exact Nat.le_of_mul_le_mul_right hbig hRpos

/-- **No overflow below `R - 2N`.** If the input value plus `2N` fits in `R = radix^9` (and
`4N ≤ R`), the raw square `T = (A² + QN)/R` keeps that bound, so its top digit stays below
`2^240` and the normalization branch is never taken. -/
theorem no_overflow (inv : UInt256) (a n : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix) (hn : ∀ i < 9, (n i).toNat < radix)
    (N : Nat) (hn0 : (n 0).toNat = N % radix) (hNvalue : value n = N)
    (hinv : (N*inv.toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hN4 : 4*N ≤ radix^9) (hbound : value a + 2*N ≤ radix^9) :
    (overflowFlag (squared inv a zeroWords n)).toNat = 0 ∧
      value (squared inv a zeroWords n) + 2*N ≤ radix^9 := by
  have hz : ∀ i < 9, (zeroWords i).toNat < radix := by
    intro i hi
    exact Nat.two_pow_pos _
  have hlow := (squareTrace inv a zeroWords n).output_low_bound ha hz hn N hn0 hinv
  have he := (squareTrace inv a zeroWords n).exact_product ha hz hn N hn0 hinv
  have hQ := weightedBound radix 9 (fun i => ((squareTrace inv a zeroWords n).q i).toNat)
    (Nat.two_pow_pos _) (squareTrace inv a zeroWords n).q_bound
  have hNv : weighted radix 9 (fun i => (n i).toNat) = N := hNvalue
  rw [hNv] at he
  have hTR := bound_step (value a) (value (squared inv a zeroWords n))
    (weighted radix 9 (fun i => ((squareTrace inv a zeroWords n).q i).toNat)) N (radix^9)
    he hQ hN4 hbound
  refine ⟨?_, hTR⟩
  have hlt : value (squared inv a zeroWords n) < (2^240)^9 := by
    change value (squared inv a zeroWords n) < radix^9
    omega
  exact (overflow_zero _ hlow).mpr hlt


#print axioms arithmetic
#print axioms no_overflow
end CycleSubmission.SquareStep
