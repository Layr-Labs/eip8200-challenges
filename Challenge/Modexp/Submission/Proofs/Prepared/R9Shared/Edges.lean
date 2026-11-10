import Challenge.Modexp.Submission.Proofs.Prepared.R9Shared.Math
set_option linter.unusedVariables false
namespace R9SharedMath0
open EvmSemantics CycleSubmission.Prepared.Arithmetic
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def qNew (a0 n0 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(a0*a0))
def cNew (a0 n0 p inv : W) : W :=
  UInt256.mulMod (N 2048) (UInt256.mulMod (qNew a0 n0 p inv) n0 p + UInt256.mulMod a0 a0 p) p
theorem old_q_matches (inv : W) (a b n : Nat → W) :
    qNew (a 0) (n 0) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareQ0 inv a b n := by
  simp only [qNew, CycleSubmission.WordHistory.squareQ0]
theorem old_c_matches (inv : W) (a b n : Nat → W) :
    cNew (a 0) (n 0) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareC1 inv a b n := by
  simp only [cNew, qNew, CycleSubmission.WordHistory.squareC1, CycleSubmission.WordHistory.squareQ0, mmC]
end R9SharedMath0
namespace R9SharedMath16
open EvmSemantics CycleSubmission.Prepared.Arithmetic
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loNew (c q8 a8 n8 p : W) : W := q8*n8+a8*a8+c
def hiNew (c q8 a8 n8 p : W) : W := UInt256.mulMod q8 n8 p+UInt256.mulMod a8 a8 p+c
def qNew (c q8 a8 n8 p : W) : W := UInt256.land (N (2^240-1)) (loNew c q8 a8 n8 p)
def cNew (c q8 a8 n8 p : W) : W := UInt256.mulMod (N 2048) (p+(hiNew c q8 a8 n8 p-qNew c q8 a8 n8 p)) p
theorem old_q_matches (inv : W) (a b n : Nat → W) :
    qNew (CycleSubmission.WordHistory.squareC16 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n)
      (a 8) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareD7 inv a b n := by
  simp only [qNew, loNew, CycleSubmission.WordHistory.squareD7, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) :
    cNew (CycleSubmission.WordHistory.squareC16 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n)
      (a 8) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareC17 inv a b n := by
  simp only [cNew, hiNew, qNew, loNew, CycleSubmission.WordHistory.squareC17,
    CycleSubmission.DirectRecovery.carry, addA, addL, addC, mulC, mmC]
end R9SharedMath16
