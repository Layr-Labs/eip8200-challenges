import Challenge.Modexp.Submission.Proofs.CRT.SequenceResult
import Challenge.Modexp.Submission.Proofs.CRT.SequencePreservation
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

namespace HistoricalSearch.KernelArithmetic
open EvmSemantics EvmSemantics.EVM
open HistoricalSearch.GeneratedArithmetic HistoricalSearch.ColumnMemory
open HistoricalSearch.ColumnSequence HistoricalSearch.MixedMontgomery
open HistoricalSearch.SequenceArithmetic HistoricalSearch.SequenceResult
open Challenge.Modexp.Submission.Proofs.Fast.Model

variable (s : State) (minv : UInt256) (n : Nat → UInt256) (rest : List UInt256)

theorem cancellation_bound : weighted radix 9 (fun i => (finalQ s minv n rest i).toNat) < 2^2048 := by
  rw [(widthParameters 244 96 (by decide) (by decide)).2]
  exact mixedCancellationBound radix (2^96) _ (Nat.two_pow_pos 244)
    (fun i hi => q_bounds s minv n rest i (by omega)) (q_top s minv n rest)

/-- Arithmetic contract of the actual sequential 17-column memory transformer.
The starting cancellation scratch is unrestricted. -/
theorem contract (A N : Nat)
    (ha : ∀ i < 9, (aRead s.memory i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (ha8 : (aRead s.memory 8).toNat < 2^96) (hn8 : (n 8).toNat < 2^96)
    (hAvalue : weighted radix 9 (fun i => (aRead s.memory i).toNat) = A)
    (hNvalue : weighted radix 9 (fun i => (n i).toNat) = N)
    (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0)
    (hAR : A < 2^2048) (hN : 0 < N) (hNR : N < 2^2048) (hodd : Odd N) :
    (∀ i < 9, (dRead (states s minv n rest 17).memory i).toNat < radix) ∧
    output s minv n rest < 2^2048+N ∧
    normalize (2^2048) N (output s minv n rest) < 2^2048 ∧
    normalize (2^2048) N (output s minv n rest) % N = montMul N (2^2048) A A := by
  have hex := exact_output s minv n rest N ha hn ha8 hn8 hn0 hinv
  rw [hAvalue, hNvalue, pow_two] at hex
  have hR : 0 < (2^2048 : Nat) := Nat.two_pow_pos 2048
  have hQ := cancellation_bound s minv n rest
  have ht : output s minv n rest =
      (A*A+weighted radix 9 (fun i => (finalQ s minv n rest i).toNat)*N) / 2^2048 := by
    rw [← hex, Nat.mul_div_cancel _ hR]
  have hr : output s minv n rest < 2^2048+N := by
    rw [ht]
    exact montgomeryRange (2^2048) N A A _ hR hN hAR hAR hQ
  have hc := arithmeticContract (2^2048) N A A _ (output s minv n rest)
    hR hN hNR hAR hAR hQ (oddModulusCoprime N hodd) hex
  exact ⟨output_digits s minv n rest ha hn ha8 hn8, hr, hc⟩

#print axioms cancellation_bound
#print axioms contract
end HistoricalSearch.KernelArithmetic
