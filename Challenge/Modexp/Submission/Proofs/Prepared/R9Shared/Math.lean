import Challenge.Modexp.Submission.Proofs.Prepared.R5Square
import Challenge.Modexp.Submission.Proofs.Cycle.SquareHistory
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace R9SharedMath1
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q0 a0 a1 n0 n1 p inv : W) : W := ([((q0)*(n1)), ((a0)*(a1)), ((a0)*(a1)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q0 a0 a1 n0 n1 p inv : W) : W := ([((q0)*(n1)), ((a0+a0)*(a1)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q0 a0 a1 n0 n1 p inv : W) : W := ([(UInt256.mulMod (q0) (n1) p), (UInt256.mulMod (a0) (a1) p), (UInt256.mulMod (a0) (a1) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q0 a0 a1 n0 n1 p inv : W) : W := ([(UInt256.mulMod (q0) (n1) p), (UInt256.mulMod (a0+a0) (a1) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q0 a0 a1 n0 n1 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loOld c q0 a0 a1 n0 n1 p inv))
def qNew (c q0 a0 a1 n0 n1 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loNew c q0 a0 a1 n0 n1 p inv))
def cOld (c q0 a0 a1 n0 n1 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qOld c q0 a0 a1 n0 n1 p inv) (n0) p)+(hiOld c q0 a0 a1 n0 n1 p inv)) p
def cNew (c q0 a0 a1 n0 n1 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qNew c q0 a0 a1 n0 n1 p inv) (n0) p)+(hiNew c q0 a0 a1 n0 n1 p inv)) p
theorem q_same (c q0 a0 a1 n0 n1 p inv : W) : qNew c q0 a0 a1 n0 n1 p inv = qOld c q0 a0 a1 n0 n1 p inv := by
  have h0 : (a0+a0)*a1 = a0*a1+a0*a1 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a0 a1
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, addA, addL, addC]
theorem c_same (c q0 a0 a1 n0 n1 p inv : W)
    (ha0 : a0.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q0 a0 a1 n0 n1 p inv = cOld c q0 a0 a1 n0 n1 p inv := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (xs.foldr (fun x y => x+y) (N 0)) p
  let ys0 : List W := [(UInt256.mulMod (qOld c q0 a0 a1 n0 n1 p inv) (n0) p), (UInt256.mulMod (q0) (n1) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_list_radix240 a0 a1 (N 2048) ys0 ha0 (by simp [ys0]) hb0
  have step0 : red [(UInt256.mulMod (qOld c q0 a0 a1 n0 n1 p inv) (n0) p), (UInt256.mulMod (q0) (n1) p), (UInt256.mulMod (a0+a0) (a1) p), c] = red [(UInt256.mulMod (qOld c q0 a0 a1 n0 n1 p inv) (n0) p), (UInt256.mulMod (q0) (n1) p), (UInt256.mulMod (a0) (a1) p), (UInt256.mulMod (a0) (a1) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using step0
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC1 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (a 0) (a 1) (n 0) (n 1) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareQ1 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareQ1, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC1 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (a 0) (a 1) (n 0) (n 1) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareC2 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC2, CycleSubmission.WordHistory.squareQ1, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath1

namespace R9SharedMath2
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := ([((q1)*(n1)), ((q0)*(n2)), ((a1)*(a1)), ((a0)*(a2)), ((a0)*(a2)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := ([((q1)*(n1)), ((q0)*(n2)), ((a1)*(a1)), ((a0+a0)*(a2)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := ([(UInt256.mulMod (q1) (n1) p), (UInt256.mulMod (q0) (n2) p), (UInt256.mulMod (a1) (a1) p), (UInt256.mulMod (a0) (a2) p), (UInt256.mulMod (a0) (a2) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := ([(UInt256.mulMod (q1) (n1) p), (UInt256.mulMod (q0) (n2) p), (UInt256.mulMod (a1) (a1) p), (UInt256.mulMod (a0+a0) (a2) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv))
def qNew (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loNew c q0 q1 a0 a1 a2 n0 n1 n2 p inv))
def cOld (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv) (n0) p)+(hiOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv)) p
def cNew (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qNew c q0 q1 a0 a1 a2 n0 n1 n2 p inv) (n0) p)+(hiNew c q0 q1 a0 a1 a2 n0 n1 n2 p inv)) p
theorem q_same (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W) : qNew c q0 q1 a0 a1 a2 n0 n1 n2 p inv = qOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv := by
  have h0 : (a0+a0)*a2 = a0*a2+a0*a2 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a0 a2
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, addA, addL, addC]
theorem c_same (c q0 q1 a0 a1 a2 n0 n1 n2 p inv : W)
    (ha0 : a0.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q0 q1 a0 a1 a2 n0 n1 n2 p inv = cOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (xs.foldr (fun x y => x+y) (N 0)) p
  let ys0 : List W := [(UInt256.mulMod (qOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv) (n0) p), (UInt256.mulMod (q1) (n1) p), (UInt256.mulMod (q0) (n2) p), (UInt256.mulMod (a1) (a1) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_list_radix240 a0 a2 (N 2048) ys0 ha0 (by simp [ys0]) hb0
  have step0 : red [(UInt256.mulMod (qOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv) (n0) p), (UInt256.mulMod (q1) (n1) p), (UInt256.mulMod (q0) (n2) p), (UInt256.mulMod (a1) (a1) p), (UInt256.mulMod (a0+a0) (a2) p), c] = red [(UInt256.mulMod (qOld c q0 q1 a0 a1 a2 n0 n1 n2 p inv) (n0) p), (UInt256.mulMod (q1) (n1) p), (UInt256.mulMod (q0) (n2) p), (UInt256.mulMod (a1) (a1) p), (UInt256.mulMod (a0) (a2) p), (UInt256.mulMod (a0) (a2) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using step0
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC2 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (a 0) (a 1) (a 2) (n 0) (n 1) (n 2) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareQ2 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareQ2, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC2 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (a 0) (a 1) (a 2) (n 0) (n 1) (n 2) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareC3 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC3, CycleSubmission.WordHistory.squareQ2, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath2

namespace R9SharedMath3
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := ([((q2)*(n1)), ((q1)*(n2)), ((q0)*(n3)), ((a0)*(a3)), ((a0)*(a3)), ((a1)*(a2)), ((a1)*(a2)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := ([((q2)*(n1)), ((q1)*(n2)), ((q0)*(n3)), ((a0+a0)*(a3)), ((a1+a1)*(a2)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := ([(UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a1) (a2) p), (UInt256.mulMod (a1) (a2) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := ([(UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0+a0) (a3) p), (UInt256.mulMod (a1+a1) (a2) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv))
def qNew (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loNew c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv))
def cOld (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p)+(hiOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv)) p
def cNew (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qNew c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p)+(hiNew c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv)) p
theorem q_same (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W) : qNew c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv = qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv := by
  have h0 : (a0+a0)*a3 = a0*a3+a0*a3 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a0 a3
  have h1 : (a1+a1)*a2 = a1*a2+a1*a2 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a1 a2
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, addA, addL, addC]
theorem c_same (c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv : W)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv = cOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (xs.foldr (fun x y => x+y) (N 0)) p
  let ys0 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p), (UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a1+a1) (a2) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_list_radix240 a0 a3 (N 2048) ys0 ha0 (by simp [ys0]) hb0
  have step0 : red [(UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p), (UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0+a0) (a3) p), (UInt256.mulMod (a1+a1) (a2) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p), (UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a1+a1) (a2) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p), (UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a0) (a3) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_list_radix240 a1 a2 (N 2048) ys1 ha1 (by simp [ys1]) hb1
  have step1 : red [(UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p), (UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a1+a1) (a2) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv) (n0) p), (UInt256.mulMod (q2) (n1) p), (UInt256.mulMod (q1) (n2) p), (UInt256.mulMod (q0) (n3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a0) (a3) p), (UInt256.mulMod (a1) (a2) p), (UInt256.mulMod (a1) (a2) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using (step0).trans step1
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC3 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (a 0) (a 1) (a 2) (a 3) (n 0) (n 1) (n 2) (n 3) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareQ3 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareQ3, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC3 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (a 0) (a 1) (a 2) (a 3) (n 0) (n 1) (n 2) (n 3) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareC4 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC4, CycleSubmission.WordHistory.squareQ3, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath3

namespace R9SharedMath4
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := ([((q3)*(n1)), ((q2)*(n2)), ((q1)*(n3)), ((q0)*(n4)), ((a2)*(a2)), ((a0)*(a4)), ((a0)*(a4)), ((a1)*(a3)), ((a1)*(a3)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := ([((q3)*(n1)), ((q2)*(n2)), ((q1)*(n3)), ((q0)*(n4)), ((a2)*(a2)), ((a0+a0)*(a4)), ((a1+a1)*(a3)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := ([(UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a1) (a3) p), (UInt256.mulMod (a1) (a3) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := ([(UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0+a0) (a4) p), (UInt256.mulMod (a1+a1) (a3) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv))
def qNew (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loNew c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv))
def cOld (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p)+(hiOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv)) p
def cNew (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qNew c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p)+(hiNew c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv)) p
theorem q_same (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W) : qNew c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv = qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv := by
  have h0 : (a0+a0)*a4 = a0*a4+a0*a4 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a0 a4
  have h1 : (a1+a1)*a3 = a1*a3+a1*a3 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a1 a3
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, addA, addL, addC]
theorem c_same (c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv : W)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv = cOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (xs.foldr (fun x y => x+y) (N 0)) p
  let ys0 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p), (UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a1+a1) (a3) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_list_radix240 a0 a4 (N 2048) ys0 ha0 (by simp [ys0]) hb0
  have step0 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p), (UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0+a0) (a4) p), (UInt256.mulMod (a1+a1) (a3) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p), (UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a1+a1) (a3) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p), (UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a0) (a4) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_list_radix240 a1 a3 (N 2048) ys1 ha1 (by simp [ys1]) hb1
  have step1 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p), (UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a1+a1) (a3) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv) (n0) p), (UInt256.mulMod (q3) (n1) p), (UInt256.mulMod (q2) (n2) p), (UInt256.mulMod (q1) (n3) p), (UInt256.mulMod (q0) (n4) p), (UInt256.mulMod (a2) (a2) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a0) (a4) p), (UInt256.mulMod (a1) (a3) p), (UInt256.mulMod (a1) (a3) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using (step0).trans step1
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC4 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (a 0) (a 1) (a 2) (a 3) (a 4) (n 0) (n 1) (n 2) (n 3) (n 4) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareQ4 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareQ4, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC4 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (a 0) (a 1) (a 2) (a 3) (a 4) (n 0) (n 1) (n 2) (n 3) (n 4) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareC5 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC5, CycleSubmission.WordHistory.squareQ4, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath4

namespace R9SharedMath5
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv : W) : W := ([((q4)*(n1)), ((q3)*(n2)), ((q2)*(n3)), ((q1)*(n4)), ((q0)*(n5)), ((a0)*(a5)), ((a0)*(a5)), ((a1)*(a4)), ((a1)*(a4)), ((a2)*(a3)), ((a2)*(a3)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv : W) : W := ([((q4)*(n1)), ((q3)*(n2)), ((q2)*(n3)), ((q1)*(n4)), ((q0)*(n5)), ((a0+a0)*(a5)), ((a1+a1)*(a4)), ((a2+a2)*(a3)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv : W) : W := ([(UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (q0) (n5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a2) (a3) p), (UInt256.mulMod (a2) (a3) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv : W) : W := ([(UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (q0) (n5) p), (UInt256.mulMod (a0+a0) (a5) p), (UInt256.mulMod (a1+a1) (a4) p), (UInt256.mulMod (a2+a2) (a3) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv))
def qNew (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loNew c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv))
def cOld (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv) (n0) p)+(hiOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv)) p
def cNew (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qNew c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv) (n0) p)+(hiNew c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv)) p
theorem q_same (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv : W) : qNew c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv = qOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv := by
  have h0 : (a0+a0)*a5 = a0*a5+a0*a5 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a0 a5
  have h1 : (a1+a1)*a4 = a1*a4+a1*a4 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a1 a4
  have h2 : (a2+a2)*a3 = a2*a3+a2*a3 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a2 a3
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, h2, addA, addL, addC]
theorem c_same (c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv : W)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv = cOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (xs.foldr (fun x y => x+y) (N 0)) p
  let ys0 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv) (n0) p), (UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (q0) (n5) p), (UInt256.mulMod (a1+a1) (a4) p), (UInt256.mulMod (a2+a2) (a3) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_list_radix240 a0 a5 (N 2048) ys0 ha0 (by simp [ys0]) hb0
  have step0 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv) (n0) p), (UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (q0) (n5) p), (UInt256.mulMod (a0+a0) (a5) p), (UInt256.mulMod (a1+a1) (a4) p), (UInt256.mulMod (a2+a2) (a3) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv) (n0) p), (UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (q0) (n5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a1+a1) (a4) p), (UInt256.mulMod (a2+a2) (a3) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv) (n0) p), (UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (q0) (n5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a2+a2) (a3) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_list_radix240 a1 a4 (N 2048) ys1 ha1 (by simp [ys1]) hb1
  have step1 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv) (n0) p), (UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (q0) (n5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a1+a1) (a4) p), (UInt256.mulMod (a2+a2) (a3) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv) (n0) p), (UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (q0) (n5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a2+a2) (a3) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  let ys2 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv) (n0) p), (UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (q0) (n5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a1) (a4) p), c]
  have hb2 : ∀ x ∈ ys2, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys2] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh2 := high_double_list_radix240 a2 a3 (N 2048) ys2 ha2 (by simp [ys2]) hb2
  have step2 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv) (n0) p), (UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (q0) (n5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a2+a2) (a3) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv) (n0) p), (UInt256.mulMod (q4) (n1) p), (UInt256.mulMod (q3) (n2) p), (UInt256.mulMod (q2) (n3) p), (UInt256.mulMod (q1) (n4) p), (UInt256.mulMod (q0) (n5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a0) (a5) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a1) (a4) p), (UInt256.mulMod (a2) (a3) p), (UInt256.mulMod (a2) (a3) p), c] := by
    simpa only [red, ys2, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh2
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using ((step0).trans step1).trans step2
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC5 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareQ5 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareQ5, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC5 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareC6 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC6, CycleSubmission.WordHistory.squareQ5, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath5

namespace R9SharedMath6
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv : W) : W := ([((q5)*(n1)), ((q4)*(n2)), ((q3)*(n3)), ((q2)*(n4)), ((q1)*(n5)), ((q0)*(n6)), ((a3)*(a3)), ((a0)*(a6)), ((a0)*(a6)), ((a1)*(a5)), ((a1)*(a5)), ((a2)*(a4)), ((a2)*(a4)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv : W) : W := ([((q5)*(n1)), ((q4)*(n2)), ((q3)*(n3)), ((q2)*(n4)), ((q1)*(n5)), ((q0)*(n6)), ((a3)*(a3)), ((a0+a0)*(a6)), ((a1+a1)*(a5)), ((a2+a2)*(a4)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv : W) : W := ([(UInt256.mulMod (q5) (n1) p), (UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (q1) (n5) p), (UInt256.mulMod (q0) (n6) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a1) (a5) p), (UInt256.mulMod (a1) (a5) p), (UInt256.mulMod (a2) (a4) p), (UInt256.mulMod (a2) (a4) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv : W) : W := ([(UInt256.mulMod (q5) (n1) p), (UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (q1) (n5) p), (UInt256.mulMod (q0) (n6) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a0+a0) (a6) p), (UInt256.mulMod (a1+a1) (a5) p), (UInt256.mulMod (a2+a2) (a4) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv))
def qNew (c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loNew c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv))
def cOld (c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv) (n0) p)+(hiOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv)) p
def cNew (c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qNew c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv) (n0) p)+(hiNew c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv)) p
theorem q_same (c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv : W) : qNew c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv = qOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv := by
  have h0 : (a0+a0)*a6 = a0*a6+a0*a6 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a0 a6
  have h1 : (a1+a1)*a5 = a1*a5+a1*a5 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a1 a5
  have h2 : (a2+a2)*a4 = a2*a4+a2*a4 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a2 a4
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, h2, addA, addL, addC]
theorem c_same (c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv : W)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv = cOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (xs.foldr (fun x y => x+y) (N 0)) p
  let ys0 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv) (n0) p), (UInt256.mulMod (q5) (n1) p), (UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (q1) (n5) p), (UInt256.mulMod (q0) (n6) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a1+a1) (a5) p), (UInt256.mulMod (a2+a2) (a4) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_list_radix240 a0 a6 (N 2048) ys0 ha0 (by simp [ys0]) hb0
  have step0 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv) (n0) p), (UInt256.mulMod (q5) (n1) p), (UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (q1) (n5) p), (UInt256.mulMod (q0) (n6) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a0+a0) (a6) p), (UInt256.mulMod (a1+a1) (a5) p), (UInt256.mulMod (a2+a2) (a4) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv) (n0) p), (UInt256.mulMod (q5) (n1) p), (UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (q1) (n5) p), (UInt256.mulMod (q0) (n6) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a1+a1) (a5) p), (UInt256.mulMod (a2+a2) (a4) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv) (n0) p), (UInt256.mulMod (q5) (n1) p), (UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (q1) (n5) p), (UInt256.mulMod (q0) (n6) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a2+a2) (a4) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_list_radix240 a1 a5 (N 2048) ys1 ha1 (by simp [ys1]) hb1
  have step1 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv) (n0) p), (UInt256.mulMod (q5) (n1) p), (UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (q1) (n5) p), (UInt256.mulMod (q0) (n6) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a1+a1) (a5) p), (UInt256.mulMod (a2+a2) (a4) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv) (n0) p), (UInt256.mulMod (q5) (n1) p), (UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (q1) (n5) p), (UInt256.mulMod (q0) (n6) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a1) (a5) p), (UInt256.mulMod (a1) (a5) p), (UInt256.mulMod (a2+a2) (a4) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  let ys2 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv) (n0) p), (UInt256.mulMod (q5) (n1) p), (UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (q1) (n5) p), (UInt256.mulMod (q0) (n6) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a1) (a5) p), (UInt256.mulMod (a1) (a5) p), c]
  have hb2 : ∀ x ∈ ys2, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys2] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh2 := high_double_list_radix240 a2 a4 (N 2048) ys2 ha2 (by simp [ys2]) hb2
  have step2 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv) (n0) p), (UInt256.mulMod (q5) (n1) p), (UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (q1) (n5) p), (UInt256.mulMod (q0) (n6) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a1) (a5) p), (UInt256.mulMod (a1) (a5) p), (UInt256.mulMod (a2+a2) (a4) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv) (n0) p), (UInt256.mulMod (q5) (n1) p), (UInt256.mulMod (q4) (n2) p), (UInt256.mulMod (q3) (n3) p), (UInt256.mulMod (q2) (n4) p), (UInt256.mulMod (q1) (n5) p), (UInt256.mulMod (q0) (n6) p), (UInt256.mulMod (a3) (a3) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a0) (a6) p), (UInt256.mulMod (a1) (a5) p), (UInt256.mulMod (a1) (a5) p), (UInt256.mulMod (a2) (a4) p), (UInt256.mulMod (a2) (a4) p), c] := by
    simpa only [red, ys2, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh2
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using ((step0).trans step1).trans step2
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC6 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareQ6 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareQ6, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC6 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareC7 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC7, CycleSubmission.WordHistory.squareQ6, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath6

namespace R9SharedMath7
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv : W) : W := ([((q6)*(n1)), ((q5)*(n2)), ((q4)*(n3)), ((q3)*(n4)), ((q2)*(n5)), ((q1)*(n6)), ((q0)*(n7)), ((a0)*(a7)), ((a0)*(a7)), ((a1)*(a6)), ((a1)*(a6)), ((a2)*(a5)), ((a2)*(a5)), ((a3)*(a4)), ((a3)*(a4)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv : W) : W := ([((q6)*(n1)), ((q5)*(n2)), ((q4)*(n3)), ((q3)*(n4)), ((q2)*(n5)), ((q1)*(n6)), ((q0)*(n7)), ((a0+a0)*(a7)), ((a1+a1)*(a6)), ((a2+a2)*(a5)), ((a3+a3)*(a4)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv : W) : W := ([(UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a2) (a5) p), (UInt256.mulMod (a2) (a5) p), (UInt256.mulMod (a3) (a4) p), (UInt256.mulMod (a3) (a4) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv : W) : W := ([(UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0+a0) (a7) p), (UInt256.mulMod (a1+a1) (a6) p), (UInt256.mulMod (a2+a2) (a5) p), (UInt256.mulMod (a3+a3) (a4) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv))
def qNew (c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loNew c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv))
def cOld (c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p)+(hiOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv)) p
def cNew (c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qNew c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p)+(hiNew c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv)) p
theorem q_same (c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv : W) : qNew c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv = qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv := by
  have h0 : (a0+a0)*a7 = a0*a7+a0*a7 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a0 a7
  have h1 : (a1+a1)*a6 = a1*a6+a1*a6 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a1 a6
  have h2 : (a2+a2)*a5 = a2*a5+a2*a5 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a2 a5
  have h3 : (a3+a3)*a4 = a3*a4+a3*a4 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a3 a4
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, h2, h3, addA, addL, addC]
theorem c_same (c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv : W)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv = cOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (xs.foldr (fun x y => x+y) (N 0)) p
  let ys0 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p), (UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a1+a1) (a6) p), (UInt256.mulMod (a2+a2) (a5) p), (UInt256.mulMod (a3+a3) (a4) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_list_radix240 a0 a7 (N 2048) ys0 ha0 (by simp [ys0]) hb0
  have step0 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p), (UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0+a0) (a7) p), (UInt256.mulMod (a1+a1) (a6) p), (UInt256.mulMod (a2+a2) (a5) p), (UInt256.mulMod (a3+a3) (a4) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p), (UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a1+a1) (a6) p), (UInt256.mulMod (a2+a2) (a5) p), (UInt256.mulMod (a3+a3) (a4) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p), (UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a2+a2) (a5) p), (UInt256.mulMod (a3+a3) (a4) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_list_radix240 a1 a6 (N 2048) ys1 ha1 (by simp [ys1]) hb1
  have step1 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p), (UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a1+a1) (a6) p), (UInt256.mulMod (a2+a2) (a5) p), (UInt256.mulMod (a3+a3) (a4) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p), (UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a2+a2) (a5) p), (UInt256.mulMod (a3+a3) (a4) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  let ys2 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p), (UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a3+a3) (a4) p), c]
  have hb2 : ∀ x ∈ ys2, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys2] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh2 := high_double_list_radix240 a2 a5 (N 2048) ys2 ha2 (by simp [ys2]) hb2
  have step2 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p), (UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a2+a2) (a5) p), (UInt256.mulMod (a3+a3) (a4) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p), (UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a2) (a5) p), (UInt256.mulMod (a2) (a5) p), (UInt256.mulMod (a3+a3) (a4) p), c] := by
    simpa only [red, ys2, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh2
  let ys3 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p), (UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a2) (a5) p), (UInt256.mulMod (a2) (a5) p), c]
  have hb3 : ∀ x ∈ ys3, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys3] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh3 := high_double_list_radix240 a3 a4 (N 2048) ys3 ha3 (by simp [ys3]) hb3
  have step3 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p), (UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a2) (a5) p), (UInt256.mulMod (a2) (a5) p), (UInt256.mulMod (a3+a3) (a4) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv) (n0) p), (UInt256.mulMod (q6) (n1) p), (UInt256.mulMod (q5) (n2) p), (UInt256.mulMod (q4) (n3) p), (UInt256.mulMod (q3) (n4) p), (UInt256.mulMod (q2) (n5) p), (UInt256.mulMod (q1) (n6) p), (UInt256.mulMod (q0) (n7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a0) (a7) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a1) (a6) p), (UInt256.mulMod (a2) (a5) p), (UInt256.mulMod (a2) (a5) p), (UInt256.mulMod (a3) (a4) p), (UInt256.mulMod (a3) (a4) p), c] := by
    simpa only [red, ys3, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh3
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using (((step0).trans step1).trans step2).trans step3
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC7 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareQ7 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareQ7, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC7 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareC8 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC8, CycleSubmission.WordHistory.squareQ7, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath7

namespace R9SharedMath8
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) : W := ([((q7)*(n1)), ((q6)*(n2)), ((q5)*(n3)), ((q4)*(n4)), ((q3)*(n5)), ((q2)*(n6)), ((q1)*(n7)), ((q0)*(n8)), ((a4)*(a4)), ((a0)*(a8)), ((a0)*(a8)), ((a1)*(a7)), ((a1)*(a7)), ((a2)*(a6)), ((a2)*(a6)), ((a3)*(a5)), ((a3)*(a5)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) : W := ([((q7)*(n1)), ((q6)*(n2)), ((q5)*(n3)), ((q4)*(n4)), ((q3)*(n5)), ((q2)*(n6)), ((q1)*(n7)), ((q0)*(n8)), ((a4)*(a4)), ((a0+a0)*(a8)), ((a1+a1)*(a7)), ((a2+a2)*(a6)), ((a3+a3)*(a5)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) : W := ([(UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a2) (a6) p), (UInt256.mulMod (a2) (a6) p), (UInt256.mulMod (a3) (a5) p), (UInt256.mulMod (a3) (a5) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) : W := ([(UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0+a0) (a8) p), (UInt256.mulMod (a1+a1) (a7) p), (UInt256.mulMod (a2+a2) (a6) p), (UInt256.mulMod (a3+a3) (a5) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv))
def qNew (c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) : W := UInt256.land (N (2^240-1)) (inv*(loNew c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv))
def cOld (c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p)+(hiOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv)) p
def cNew (c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) : W := UInt256.mulMod (N 2048) ((UInt256.mulMod (qNew c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p)+(hiNew c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv)) p
theorem q_same (c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) : qNew c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv = qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv := by
  have h0 : (a0+a0)*a8 = a0*a8+a0*a8 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a0 a8
  have h1 : (a1+a1)*a7 = a1*a7+a1*a7 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a1 a7
  have h2 : (a2+a2)*a6 = a2*a6+a2*a6 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a2 a6
  have h3 : (a3+a3)*a5 = a3*a5+a3*a5 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a3 a5
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, h2, h3, addA, addL, addC]
theorem c_same (c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W)
    (ha0 : a0.toNat < 2^240) (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv = cOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (xs.foldr (fun x y => x+y) (N 0)) p
  let ys0 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p), (UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a1+a1) (a7) p), (UInt256.mulMod (a2+a2) (a6) p), (UInt256.mulMod (a3+a3) (a5) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_list_radix240 a0 a8 (N 2048) ys0 ha0 (by simp [ys0]) hb0
  have step0 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p), (UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0+a0) (a8) p), (UInt256.mulMod (a1+a1) (a7) p), (UInt256.mulMod (a2+a2) (a6) p), (UInt256.mulMod (a3+a3) (a5) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p), (UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a1+a1) (a7) p), (UInt256.mulMod (a2+a2) (a6) p), (UInt256.mulMod (a3+a3) (a5) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p), (UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a2+a2) (a6) p), (UInt256.mulMod (a3+a3) (a5) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_list_radix240 a1 a7 (N 2048) ys1 ha1 (by simp [ys1]) hb1
  have step1 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p), (UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a1+a1) (a7) p), (UInt256.mulMod (a2+a2) (a6) p), (UInt256.mulMod (a3+a3) (a5) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p), (UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a2+a2) (a6) p), (UInt256.mulMod (a3+a3) (a5) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  let ys2 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p), (UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a3+a3) (a5) p), c]
  have hb2 : ∀ x ∈ ys2, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys2] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh2 := high_double_list_radix240 a2 a6 (N 2048) ys2 ha2 (by simp [ys2]) hb2
  have step2 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p), (UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a2+a2) (a6) p), (UInt256.mulMod (a3+a3) (a5) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p), (UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a2) (a6) p), (UInt256.mulMod (a2) (a6) p), (UInt256.mulMod (a3+a3) (a5) p), c] := by
    simpa only [red, ys2, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh2
  let ys3 : List W := [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p), (UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a2) (a6) p), (UInt256.mulMod (a2) (a6) p), c]
  have hb3 : ∀ x ∈ ys3, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys3] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh3 := high_double_list_radix240 a3 a5 (N 2048) ys3 ha3 (by simp [ys3]) hb3
  have step3 : red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p), (UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a2) (a6) p), (UInt256.mulMod (a2) (a6) p), (UInt256.mulMod (a3+a3) (a5) p), c] = red [(UInt256.mulMod (qOld c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv) (n0) p), (UInt256.mulMod (q7) (n1) p), (UInt256.mulMod (q6) (n2) p), (UInt256.mulMod (q5) (n3) p), (UInt256.mulMod (q4) (n4) p), (UInt256.mulMod (q3) (n5) p), (UInt256.mulMod (q2) (n6) p), (UInt256.mulMod (q1) (n7) p), (UInt256.mulMod (q0) (n8) p), (UInt256.mulMod (a4) (a4) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a0) (a8) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a1) (a7) p), (UInt256.mulMod (a2) (a6) p), (UInt256.mulMod (a2) (a6) p), (UInt256.mulMod (a3) (a5) p), (UInt256.mulMod (a3) (a5) p), c] := by
    simpa only [red, ys3, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh3
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using (((step0).trans step1).trans step2).trans step3
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC8 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareQ8 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareQ8, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC8 inv a b n) (CycleSubmission.WordHistory.squareQ0 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P inv = CycleSubmission.WordHistory.squareC9 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC9, CycleSubmission.WordHistory.squareQ8, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath8

namespace R9SharedMath9
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p : W) : W := ([((q8)*(n1)), ((q7)*(n2)), ((q6)*(n3)), ((q5)*(n4)), ((q4)*(n5)), ((q3)*(n6)), ((q2)*(n7)), ((q1)*(n8)), ((a1)*(a8)), ((a1)*(a8)), ((a2)*(a7)), ((a2)*(a7)), ((a3)*(a6)), ((a3)*(a6)), ((a4)*(a5)), ((a4)*(a5)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p : W) : W := ([((q8)*(n1)), ((q7)*(n2)), ((q6)*(n3)), ((q5)*(n4)), ((q4)*(n5)), ((q3)*(n6)), ((q2)*(n7)), ((q1)*(n8)), ((a1+a1)*(a8)), ((a2+a2)*(a7)), ((a3+a3)*(a6)), ((a4+a4)*(a5)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a3) (a6) p), (UInt256.mulMod (a3) (a6) p), (UInt256.mulMod (a4) (a5) p), (UInt256.mulMod (a4) (a5) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1+a1) (a8) p), (UInt256.mulMod (a2+a2) (a7) p), (UInt256.mulMod (a3+a3) (a6) p), (UInt256.mulMod (a4+a4) (a5) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loOld c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p)
def qNew (c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loNew c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p)
def cOld (c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiOld c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p)-(qOld c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p))) p
def cNew (c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiNew c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p)-(qNew c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p))) p
theorem q_same (c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p : W) : qNew c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p = qOld c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p := by
  have h0 : (a1+a1)*a8 = a1*a8+a1*a8 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a1 a8
  have h1 : (a2+a2)*a7 = a2*a7+a2*a7 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a2 a7
  have h2 : (a3+a3)*a6 = a3*a6+a3*a6 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a3 a6
  have h3 : (a4+a4)*a5 = a4*a5+a4*a5 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a4 a5
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, h2, h3, addA, addL, addC]
theorem c_same (c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p : W)
    (ha1 : a1.toNat < 2^240) (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240) (ha4 : a4.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p = cOld c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (p+((xs.foldr (fun x y => x+y) (N 0))-(qOld c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p))) p
  have hd : (qOld c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p).toNat < p.toNat := mask240_lt_p (loOld c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p)
  let ys0 : List W := [(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a2+a2) (a7) p), (UInt256.mulMod (a3+a3) (a6) p), (UInt256.mulMod (a4+a4) (a5) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_biased_list_radix240 a1 a8 (N 2048) (qOld c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p) ys0 ha1 (by simp [ys0]) hb0 hd
  have step0 : red [(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1+a1) (a8) p), (UInt256.mulMod (a2+a2) (a7) p), (UInt256.mulMod (a3+a3) (a6) p), (UInt256.mulMod (a4+a4) (a5) p), c] = red [(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a2+a2) (a7) p), (UInt256.mulMod (a3+a3) (a6) p), (UInt256.mulMod (a4+a4) (a5) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a3+a3) (a6) p), (UInt256.mulMod (a4+a4) (a5) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_biased_list_radix240 a2 a7 (N 2048) (qOld c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p) ys1 ha2 (by simp [ys1]) hb1 hd
  have step1 : red [(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a2+a2) (a7) p), (UInt256.mulMod (a3+a3) (a6) p), (UInt256.mulMod (a4+a4) (a5) p), c] = red [(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a3+a3) (a6) p), (UInt256.mulMod (a4+a4) (a5) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  let ys2 : List W := [(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a4+a4) (a5) p), c]
  have hb2 : ∀ x ∈ ys2, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys2] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh2 := high_double_biased_list_radix240 a3 a6 (N 2048) (qOld c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p) ys2 ha3 (by simp [ys2]) hb2 hd
  have step2 : red [(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a3+a3) (a6) p), (UInt256.mulMod (a4+a4) (a5) p), c] = red [(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a3) (a6) p), (UInt256.mulMod (a3) (a6) p), (UInt256.mulMod (a4+a4) (a5) p), c] := by
    simpa only [red, ys2, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh2
  let ys3 : List W := [(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a3) (a6) p), (UInt256.mulMod (a3) (a6) p), c]
  have hb3 : ∀ x ∈ ys3, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys3] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh3 := high_double_biased_list_radix240 a4 a5 (N 2048) (qOld c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p) ys3 ha4 (by simp [ys3]) hb3 hd
  have step3 : red [(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a3) (a6) p), (UInt256.mulMod (a3) (a6) p), (UInt256.mulMod (a4+a4) (a5) p), c] = red [(UInt256.mulMod (q8) (n1) p), (UInt256.mulMod (q7) (n2) p), (UInt256.mulMod (q6) (n3) p), (UInt256.mulMod (q5) (n4) p), (UInt256.mulMod (q4) (n5) p), (UInt256.mulMod (q3) (n6) p), (UInt256.mulMod (q2) (n7) p), (UInt256.mulMod (q1) (n8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a1) (a8) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a2) (a7) p), (UInt256.mulMod (a3) (a6) p), (UInt256.mulMod (a3) (a6) p), (UInt256.mulMod (a4) (a5) p), (UInt256.mulMod (a4) (a5) p), c] := by
    simpa only [red, ys3, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh3
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using (((step0).trans step1).trans step2).trans step3
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC9 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareD0 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareD0, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC9 inv a b n) (CycleSubmission.WordHistory.squareQ1 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareC10 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC10, CycleSubmission.DirectRecovery.carry, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath9

namespace R9SharedMath10
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p : W) : W := ([((q8)*(n2)), ((q7)*(n3)), ((q6)*(n4)), ((q5)*(n5)), ((q4)*(n6)), ((q3)*(n7)), ((q2)*(n8)), ((a5)*(a5)), ((a2)*(a8)), ((a2)*(a8)), ((a3)*(a7)), ((a3)*(a7)), ((a4)*(a6)), ((a4)*(a6)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p : W) : W := ([((q8)*(n2)), ((q7)*(n3)), ((q6)*(n4)), ((q5)*(n5)), ((q4)*(n6)), ((q3)*(n7)), ((q2)*(n8)), ((a5)*(a5)), ((a2+a2)*(a8)), ((a3+a3)*(a7)), ((a4+a4)*(a6)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n2) p), (UInt256.mulMod (q7) (n3) p), (UInt256.mulMod (q6) (n4) p), (UInt256.mulMod (q5) (n5) p), (UInt256.mulMod (q4) (n6) p), (UInt256.mulMod (q3) (n7) p), (UInt256.mulMod (q2) (n8) p), (UInt256.mulMod (a5) (a5) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a3) (a7) p), (UInt256.mulMod (a3) (a7) p), (UInt256.mulMod (a4) (a6) p), (UInt256.mulMod (a4) (a6) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n2) p), (UInt256.mulMod (q7) (n3) p), (UInt256.mulMod (q6) (n4) p), (UInt256.mulMod (q5) (n5) p), (UInt256.mulMod (q4) (n6) p), (UInt256.mulMod (q3) (n7) p), (UInt256.mulMod (q2) (n8) p), (UInt256.mulMod (a5) (a5) p), (UInt256.mulMod (a2+a2) (a8) p), (UInt256.mulMod (a3+a3) (a7) p), (UInt256.mulMod (a4+a4) (a6) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loOld c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p)
def qNew (c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loNew c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p)
def cOld (c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiOld c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p)-(qOld c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p))) p
def cNew (c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiNew c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p)-(qNew c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p))) p
theorem q_same (c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p : W) : qNew c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p = qOld c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p := by
  have h0 : (a2+a2)*a8 = a2*a8+a2*a8 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a2 a8
  have h1 : (a3+a3)*a7 = a3*a7+a3*a7 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a3 a7
  have h2 : (a4+a4)*a6 = a4*a6+a4*a6 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a4 a6
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, h2, addA, addL, addC]
theorem c_same (c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p : W)
    (ha2 : a2.toNat < 2^240) (ha3 : a3.toNat < 2^240) (ha4 : a4.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p = cOld c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (p+((xs.foldr (fun x y => x+y) (N 0))-(qOld c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p))) p
  have hd : (qOld c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p).toNat < p.toNat := mask240_lt_p (loOld c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p)
  let ys0 : List W := [(UInt256.mulMod (q8) (n2) p), (UInt256.mulMod (q7) (n3) p), (UInt256.mulMod (q6) (n4) p), (UInt256.mulMod (q5) (n5) p), (UInt256.mulMod (q4) (n6) p), (UInt256.mulMod (q3) (n7) p), (UInt256.mulMod (q2) (n8) p), (UInt256.mulMod (a5) (a5) p), (UInt256.mulMod (a3+a3) (a7) p), (UInt256.mulMod (a4+a4) (a6) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_biased_list_radix240 a2 a8 (N 2048) (qOld c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p) ys0 ha2 (by simp [ys0]) hb0 hd
  have step0 : red [(UInt256.mulMod (q8) (n2) p), (UInt256.mulMod (q7) (n3) p), (UInt256.mulMod (q6) (n4) p), (UInt256.mulMod (q5) (n5) p), (UInt256.mulMod (q4) (n6) p), (UInt256.mulMod (q3) (n7) p), (UInt256.mulMod (q2) (n8) p), (UInt256.mulMod (a5) (a5) p), (UInt256.mulMod (a2+a2) (a8) p), (UInt256.mulMod (a3+a3) (a7) p), (UInt256.mulMod (a4+a4) (a6) p), c] = red [(UInt256.mulMod (q8) (n2) p), (UInt256.mulMod (q7) (n3) p), (UInt256.mulMod (q6) (n4) p), (UInt256.mulMod (q5) (n5) p), (UInt256.mulMod (q4) (n6) p), (UInt256.mulMod (q3) (n7) p), (UInt256.mulMod (q2) (n8) p), (UInt256.mulMod (a5) (a5) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a3+a3) (a7) p), (UInt256.mulMod (a4+a4) (a6) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (q8) (n2) p), (UInt256.mulMod (q7) (n3) p), (UInt256.mulMod (q6) (n4) p), (UInt256.mulMod (q5) (n5) p), (UInt256.mulMod (q4) (n6) p), (UInt256.mulMod (q3) (n7) p), (UInt256.mulMod (q2) (n8) p), (UInt256.mulMod (a5) (a5) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a4+a4) (a6) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_biased_list_radix240 a3 a7 (N 2048) (qOld c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p) ys1 ha3 (by simp [ys1]) hb1 hd
  have step1 : red [(UInt256.mulMod (q8) (n2) p), (UInt256.mulMod (q7) (n3) p), (UInt256.mulMod (q6) (n4) p), (UInt256.mulMod (q5) (n5) p), (UInt256.mulMod (q4) (n6) p), (UInt256.mulMod (q3) (n7) p), (UInt256.mulMod (q2) (n8) p), (UInt256.mulMod (a5) (a5) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a3+a3) (a7) p), (UInt256.mulMod (a4+a4) (a6) p), c] = red [(UInt256.mulMod (q8) (n2) p), (UInt256.mulMod (q7) (n3) p), (UInt256.mulMod (q6) (n4) p), (UInt256.mulMod (q5) (n5) p), (UInt256.mulMod (q4) (n6) p), (UInt256.mulMod (q3) (n7) p), (UInt256.mulMod (q2) (n8) p), (UInt256.mulMod (a5) (a5) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a3) (a7) p), (UInt256.mulMod (a3) (a7) p), (UInt256.mulMod (a4+a4) (a6) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  let ys2 : List W := [(UInt256.mulMod (q8) (n2) p), (UInt256.mulMod (q7) (n3) p), (UInt256.mulMod (q6) (n4) p), (UInt256.mulMod (q5) (n5) p), (UInt256.mulMod (q4) (n6) p), (UInt256.mulMod (q3) (n7) p), (UInt256.mulMod (q2) (n8) p), (UInt256.mulMod (a5) (a5) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a3) (a7) p), (UInt256.mulMod (a3) (a7) p), c]
  have hb2 : ∀ x ∈ ys2, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys2] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh2 := high_double_biased_list_radix240 a4 a6 (N 2048) (qOld c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p) ys2 ha4 (by simp [ys2]) hb2 hd
  have step2 : red [(UInt256.mulMod (q8) (n2) p), (UInt256.mulMod (q7) (n3) p), (UInt256.mulMod (q6) (n4) p), (UInt256.mulMod (q5) (n5) p), (UInt256.mulMod (q4) (n6) p), (UInt256.mulMod (q3) (n7) p), (UInt256.mulMod (q2) (n8) p), (UInt256.mulMod (a5) (a5) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a3) (a7) p), (UInt256.mulMod (a3) (a7) p), (UInt256.mulMod (a4+a4) (a6) p), c] = red [(UInt256.mulMod (q8) (n2) p), (UInt256.mulMod (q7) (n3) p), (UInt256.mulMod (q6) (n4) p), (UInt256.mulMod (q5) (n5) p), (UInt256.mulMod (q4) (n6) p), (UInt256.mulMod (q3) (n7) p), (UInt256.mulMod (q2) (n8) p), (UInt256.mulMod (a5) (a5) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a2) (a8) p), (UInt256.mulMod (a3) (a7) p), (UInt256.mulMod (a3) (a7) p), (UInt256.mulMod (a4) (a6) p), (UInt256.mulMod (a4) (a6) p), c] := by
    simpa only [red, ys2, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh2
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using ((step0).trans step1).trans step2
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC10 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareD1 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareD1, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC10 inv a b n) (CycleSubmission.WordHistory.squareQ2 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareC11 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC11, CycleSubmission.DirectRecovery.carry, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath10

namespace R9SharedMath11
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p : W) : W := ([((q8)*(n3)), ((q7)*(n4)), ((q6)*(n5)), ((q5)*(n6)), ((q4)*(n7)), ((q3)*(n8)), ((a3)*(a8)), ((a3)*(a8)), ((a4)*(a7)), ((a4)*(a7)), ((a5)*(a6)), ((a5)*(a6)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p : W) : W := ([((q8)*(n3)), ((q7)*(n4)), ((q6)*(n5)), ((q5)*(n6)), ((q4)*(n7)), ((q3)*(n8)), ((a3+a3)*(a8)), ((a4+a4)*(a7)), ((a5+a5)*(a6)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n3) p), (UInt256.mulMod (q7) (n4) p), (UInt256.mulMod (q6) (n5) p), (UInt256.mulMod (q5) (n6) p), (UInt256.mulMod (q4) (n7) p), (UInt256.mulMod (q3) (n8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a4) (a7) p), (UInt256.mulMod (a4) (a7) p), (UInt256.mulMod (a5) (a6) p), (UInt256.mulMod (a5) (a6) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n3) p), (UInt256.mulMod (q7) (n4) p), (UInt256.mulMod (q6) (n5) p), (UInt256.mulMod (q5) (n6) p), (UInt256.mulMod (q4) (n7) p), (UInt256.mulMod (q3) (n8) p), (UInt256.mulMod (a3+a3) (a8) p), (UInt256.mulMod (a4+a4) (a7) p), (UInt256.mulMod (a5+a5) (a6) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loOld c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p)
def qNew (c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loNew c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p)
def cOld (c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiOld c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p)-(qOld c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p))) p
def cNew (c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiNew c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p)-(qNew c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p))) p
theorem q_same (c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p : W) : qNew c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p = qOld c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p := by
  have h0 : (a3+a3)*a8 = a3*a8+a3*a8 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a3 a8
  have h1 : (a4+a4)*a7 = a4*a7+a4*a7 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a4 a7
  have h2 : (a5+a5)*a6 = a5*a6+a5*a6 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a5 a6
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, h2, addA, addL, addC]
theorem c_same (c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p : W)
    (ha3 : a3.toNat < 2^240) (ha4 : a4.toNat < 2^240) (ha5 : a5.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p = cOld c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (p+((xs.foldr (fun x y => x+y) (N 0))-(qOld c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p))) p
  have hd : (qOld c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p).toNat < p.toNat := mask240_lt_p (loOld c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p)
  let ys0 : List W := [(UInt256.mulMod (q8) (n3) p), (UInt256.mulMod (q7) (n4) p), (UInt256.mulMod (q6) (n5) p), (UInt256.mulMod (q5) (n6) p), (UInt256.mulMod (q4) (n7) p), (UInt256.mulMod (q3) (n8) p), (UInt256.mulMod (a4+a4) (a7) p), (UInt256.mulMod (a5+a5) (a6) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_biased_list_radix240 a3 a8 (N 2048) (qOld c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p) ys0 ha3 (by simp [ys0]) hb0 hd
  have step0 : red [(UInt256.mulMod (q8) (n3) p), (UInt256.mulMod (q7) (n4) p), (UInt256.mulMod (q6) (n5) p), (UInt256.mulMod (q5) (n6) p), (UInt256.mulMod (q4) (n7) p), (UInt256.mulMod (q3) (n8) p), (UInt256.mulMod (a3+a3) (a8) p), (UInt256.mulMod (a4+a4) (a7) p), (UInt256.mulMod (a5+a5) (a6) p), c] = red [(UInt256.mulMod (q8) (n3) p), (UInt256.mulMod (q7) (n4) p), (UInt256.mulMod (q6) (n5) p), (UInt256.mulMod (q5) (n6) p), (UInt256.mulMod (q4) (n7) p), (UInt256.mulMod (q3) (n8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a4+a4) (a7) p), (UInt256.mulMod (a5+a5) (a6) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (q8) (n3) p), (UInt256.mulMod (q7) (n4) p), (UInt256.mulMod (q6) (n5) p), (UInt256.mulMod (q5) (n6) p), (UInt256.mulMod (q4) (n7) p), (UInt256.mulMod (q3) (n8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a5+a5) (a6) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_biased_list_radix240 a4 a7 (N 2048) (qOld c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p) ys1 ha4 (by simp [ys1]) hb1 hd
  have step1 : red [(UInt256.mulMod (q8) (n3) p), (UInt256.mulMod (q7) (n4) p), (UInt256.mulMod (q6) (n5) p), (UInt256.mulMod (q5) (n6) p), (UInt256.mulMod (q4) (n7) p), (UInt256.mulMod (q3) (n8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a4+a4) (a7) p), (UInt256.mulMod (a5+a5) (a6) p), c] = red [(UInt256.mulMod (q8) (n3) p), (UInt256.mulMod (q7) (n4) p), (UInt256.mulMod (q6) (n5) p), (UInt256.mulMod (q5) (n6) p), (UInt256.mulMod (q4) (n7) p), (UInt256.mulMod (q3) (n8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a4) (a7) p), (UInt256.mulMod (a4) (a7) p), (UInt256.mulMod (a5+a5) (a6) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  let ys2 : List W := [(UInt256.mulMod (q8) (n3) p), (UInt256.mulMod (q7) (n4) p), (UInt256.mulMod (q6) (n5) p), (UInt256.mulMod (q5) (n6) p), (UInt256.mulMod (q4) (n7) p), (UInt256.mulMod (q3) (n8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a4) (a7) p), (UInt256.mulMod (a4) (a7) p), c]
  have hb2 : ∀ x ∈ ys2, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys2] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh2 := high_double_biased_list_radix240 a5 a6 (N 2048) (qOld c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p) ys2 ha5 (by simp [ys2]) hb2 hd
  have step2 : red [(UInt256.mulMod (q8) (n3) p), (UInt256.mulMod (q7) (n4) p), (UInt256.mulMod (q6) (n5) p), (UInt256.mulMod (q5) (n6) p), (UInt256.mulMod (q4) (n7) p), (UInt256.mulMod (q3) (n8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a4) (a7) p), (UInt256.mulMod (a4) (a7) p), (UInt256.mulMod (a5+a5) (a6) p), c] = red [(UInt256.mulMod (q8) (n3) p), (UInt256.mulMod (q7) (n4) p), (UInt256.mulMod (q6) (n5) p), (UInt256.mulMod (q5) (n6) p), (UInt256.mulMod (q4) (n7) p), (UInt256.mulMod (q3) (n8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a3) (a8) p), (UInt256.mulMod (a4) (a7) p), (UInt256.mulMod (a4) (a7) p), (UInt256.mulMod (a5) (a6) p), (UInt256.mulMod (a5) (a6) p), c] := by
    simpa only [red, ys2, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh2
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using ((step0).trans step1).trans step2
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC11 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareD2 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareD2, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC11 inv a b n) (CycleSubmission.WordHistory.squareQ3 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareC12 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC12, CycleSubmission.DirectRecovery.carry, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath11

namespace R9SharedMath12
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p : W) : W := ([((q8)*(n4)), ((q7)*(n5)), ((q6)*(n6)), ((q5)*(n7)), ((q4)*(n8)), ((a6)*(a6)), ((a4)*(a8)), ((a4)*(a8)), ((a5)*(a7)), ((a5)*(a7)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p : W) : W := ([((q8)*(n4)), ((q7)*(n5)), ((q6)*(n6)), ((q5)*(n7)), ((q4)*(n8)), ((a6)*(a6)), ((a4+a4)*(a8)), ((a5+a5)*(a7)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n4) p), (UInt256.mulMod (q7) (n5) p), (UInt256.mulMod (q6) (n6) p), (UInt256.mulMod (q5) (n7) p), (UInt256.mulMod (q4) (n8) p), (UInt256.mulMod (a6) (a6) p), (UInt256.mulMod (a4) (a8) p), (UInt256.mulMod (a4) (a8) p), (UInt256.mulMod (a5) (a7) p), (UInt256.mulMod (a5) (a7) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n4) p), (UInt256.mulMod (q7) (n5) p), (UInt256.mulMod (q6) (n6) p), (UInt256.mulMod (q5) (n7) p), (UInt256.mulMod (q4) (n8) p), (UInt256.mulMod (a6) (a6) p), (UInt256.mulMod (a4+a4) (a8) p), (UInt256.mulMod (a5+a5) (a7) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loOld c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p)
def qNew (c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loNew c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p)
def cOld (c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiOld c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p)-(qOld c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p))) p
def cNew (c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiNew c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p)-(qNew c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p))) p
theorem q_same (c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p : W) : qNew c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p = qOld c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p := by
  have h0 : (a4+a4)*a8 = a4*a8+a4*a8 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a4 a8
  have h1 : (a5+a5)*a7 = a5*a7+a5*a7 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a5 a7
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, addA, addL, addC]
theorem c_same (c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p : W)
    (ha4 : a4.toNat < 2^240) (ha5 : a5.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p = cOld c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (p+((xs.foldr (fun x y => x+y) (N 0))-(qOld c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p))) p
  have hd : (qOld c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p).toNat < p.toNat := mask240_lt_p (loOld c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p)
  let ys0 : List W := [(UInt256.mulMod (q8) (n4) p), (UInt256.mulMod (q7) (n5) p), (UInt256.mulMod (q6) (n6) p), (UInt256.mulMod (q5) (n7) p), (UInt256.mulMod (q4) (n8) p), (UInt256.mulMod (a6) (a6) p), (UInt256.mulMod (a5+a5) (a7) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_biased_list_radix240 a4 a8 (N 2048) (qOld c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p) ys0 ha4 (by simp [ys0]) hb0 hd
  have step0 : red [(UInt256.mulMod (q8) (n4) p), (UInt256.mulMod (q7) (n5) p), (UInt256.mulMod (q6) (n6) p), (UInt256.mulMod (q5) (n7) p), (UInt256.mulMod (q4) (n8) p), (UInt256.mulMod (a6) (a6) p), (UInt256.mulMod (a4+a4) (a8) p), (UInt256.mulMod (a5+a5) (a7) p), c] = red [(UInt256.mulMod (q8) (n4) p), (UInt256.mulMod (q7) (n5) p), (UInt256.mulMod (q6) (n6) p), (UInt256.mulMod (q5) (n7) p), (UInt256.mulMod (q4) (n8) p), (UInt256.mulMod (a6) (a6) p), (UInt256.mulMod (a4) (a8) p), (UInt256.mulMod (a4) (a8) p), (UInt256.mulMod (a5+a5) (a7) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (q8) (n4) p), (UInt256.mulMod (q7) (n5) p), (UInt256.mulMod (q6) (n6) p), (UInt256.mulMod (q5) (n7) p), (UInt256.mulMod (q4) (n8) p), (UInt256.mulMod (a6) (a6) p), (UInt256.mulMod (a4) (a8) p), (UInt256.mulMod (a4) (a8) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_biased_list_radix240 a5 a7 (N 2048) (qOld c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p) ys1 ha5 (by simp [ys1]) hb1 hd
  have step1 : red [(UInt256.mulMod (q8) (n4) p), (UInt256.mulMod (q7) (n5) p), (UInt256.mulMod (q6) (n6) p), (UInt256.mulMod (q5) (n7) p), (UInt256.mulMod (q4) (n8) p), (UInt256.mulMod (a6) (a6) p), (UInt256.mulMod (a4) (a8) p), (UInt256.mulMod (a4) (a8) p), (UInt256.mulMod (a5+a5) (a7) p), c] = red [(UInt256.mulMod (q8) (n4) p), (UInt256.mulMod (q7) (n5) p), (UInt256.mulMod (q6) (n6) p), (UInt256.mulMod (q5) (n7) p), (UInt256.mulMod (q4) (n8) p), (UInt256.mulMod (a6) (a6) p), (UInt256.mulMod (a4) (a8) p), (UInt256.mulMod (a4) (a8) p), (UInt256.mulMod (a5) (a7) p), (UInt256.mulMod (a5) (a7) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using (step0).trans step1
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC12 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 4) (a 5) (a 6) (a 7) (a 8) (n 4) (n 5) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareD3 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareD3, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC12 inv a b n) (CycleSubmission.WordHistory.squareQ4 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 4) (a 5) (a 6) (a 7) (a 8) (n 4) (n 5) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareC13 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC13, CycleSubmission.DirectRecovery.carry, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath12

namespace R9SharedMath13
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p : W) : W := ([((q8)*(n5)), ((q7)*(n6)), ((q6)*(n7)), ((q5)*(n8)), ((a5)*(a8)), ((a5)*(a8)), ((a6)*(a7)), ((a6)*(a7)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p : W) : W := ([((q8)*(n5)), ((q7)*(n6)), ((q6)*(n7)), ((q5)*(n8)), ((a5+a5)*(a8)), ((a6+a6)*(a7)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n5) p), (UInt256.mulMod (q7) (n6) p), (UInt256.mulMod (q6) (n7) p), (UInt256.mulMod (q5) (n8) p), (UInt256.mulMod (a5) (a8) p), (UInt256.mulMod (a5) (a8) p), (UInt256.mulMod (a6) (a7) p), (UInt256.mulMod (a6) (a7) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n5) p), (UInt256.mulMod (q7) (n6) p), (UInt256.mulMod (q6) (n7) p), (UInt256.mulMod (q5) (n8) p), (UInt256.mulMod (a5+a5) (a8) p), (UInt256.mulMod (a6+a6) (a7) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loOld c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p)
def qNew (c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loNew c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p)
def cOld (c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiOld c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p)-(qOld c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p))) p
def cNew (c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiNew c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p)-(qNew c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p))) p
theorem q_same (c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p : W) : qNew c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p = qOld c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p := by
  have h0 : (a5+a5)*a8 = a5*a8+a5*a8 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a5 a8
  have h1 : (a6+a6)*a7 = a6*a7+a6*a7 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a6 a7
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, h1, addA, addL, addC]
theorem c_same (c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p : W)
    (ha5 : a5.toNat < 2^240) (ha6 : a6.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p = cOld c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (p+((xs.foldr (fun x y => x+y) (N 0))-(qOld c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p))) p
  have hd : (qOld c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p).toNat < p.toNat := mask240_lt_p (loOld c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p)
  let ys0 : List W := [(UInt256.mulMod (q8) (n5) p), (UInt256.mulMod (q7) (n6) p), (UInt256.mulMod (q6) (n7) p), (UInt256.mulMod (q5) (n8) p), (UInt256.mulMod (a6+a6) (a7) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_biased_list_radix240 a5 a8 (N 2048) (qOld c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p) ys0 ha5 (by simp [ys0]) hb0 hd
  have step0 : red [(UInt256.mulMod (q8) (n5) p), (UInt256.mulMod (q7) (n6) p), (UInt256.mulMod (q6) (n7) p), (UInt256.mulMod (q5) (n8) p), (UInt256.mulMod (a5+a5) (a8) p), (UInt256.mulMod (a6+a6) (a7) p), c] = red [(UInt256.mulMod (q8) (n5) p), (UInt256.mulMod (q7) (n6) p), (UInt256.mulMod (q6) (n7) p), (UInt256.mulMod (q5) (n8) p), (UInt256.mulMod (a5) (a8) p), (UInt256.mulMod (a5) (a8) p), (UInt256.mulMod (a6+a6) (a7) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  let ys1 : List W := [(UInt256.mulMod (q8) (n5) p), (UInt256.mulMod (q7) (n6) p), (UInt256.mulMod (q6) (n7) p), (UInt256.mulMod (q5) (n8) p), (UInt256.mulMod (a5) (a8) p), (UInt256.mulMod (a5) (a8) p), c]
  have hb1 : ∀ x ∈ ys1, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys1] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh1 := high_double_biased_list_radix240 a6 a7 (N 2048) (qOld c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p) ys1 ha6 (by simp [ys1]) hb1 hd
  have step1 : red [(UInt256.mulMod (q8) (n5) p), (UInt256.mulMod (q7) (n6) p), (UInt256.mulMod (q6) (n7) p), (UInt256.mulMod (q5) (n8) p), (UInt256.mulMod (a5) (a8) p), (UInt256.mulMod (a5) (a8) p), (UInt256.mulMod (a6+a6) (a7) p), c] = red [(UInt256.mulMod (q8) (n5) p), (UInt256.mulMod (q7) (n6) p), (UInt256.mulMod (q6) (n7) p), (UInt256.mulMod (q5) (n8) p), (UInt256.mulMod (a5) (a8) p), (UInt256.mulMod (a5) (a8) p), (UInt256.mulMod (a6) (a7) p), (UInt256.mulMod (a6) (a7) p), c] := by
    simpa only [red, ys1, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh1
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using (step0).trans step1
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC13 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 5) (a 6) (a 7) (a 8) (n 5) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareD4 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareD4, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC13 inv a b n) (CycleSubmission.WordHistory.squareQ5 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 5) (a 6) (a 7) (a 8) (n 5) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareC14 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC14, CycleSubmission.DirectRecovery.carry, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath13

namespace R9SharedMath14
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q6 q7 q8 a6 a7 a8 n6 n7 n8 p : W) : W := ([((q8)*(n6)), ((q7)*(n7)), ((q6)*(n8)), ((a7)*(a7)), ((a6)*(a8)), ((a6)*(a8)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q6 q7 q8 a6 a7 a8 n6 n7 n8 p : W) : W := ([((q8)*(n6)), ((q7)*(n7)), ((q6)*(n8)), ((a7)*(a7)), ((a6+a6)*(a8)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q6 q7 q8 a6 a7 a8 n6 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n6) p), (UInt256.mulMod (q7) (n7) p), (UInt256.mulMod (q6) (n8) p), (UInt256.mulMod (a7) (a7) p), (UInt256.mulMod (a6) (a8) p), (UInt256.mulMod (a6) (a8) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q6 q7 q8 a6 a7 a8 n6 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n6) p), (UInt256.mulMod (q7) (n7) p), (UInt256.mulMod (q6) (n8) p), (UInt256.mulMod (a7) (a7) p), (UInt256.mulMod (a6+a6) (a8) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q6 q7 q8 a6 a7 a8 n6 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loOld c q6 q7 q8 a6 a7 a8 n6 n7 n8 p)
def qNew (c q6 q7 q8 a6 a7 a8 n6 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loNew c q6 q7 q8 a6 a7 a8 n6 n7 n8 p)
def cOld (c q6 q7 q8 a6 a7 a8 n6 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiOld c q6 q7 q8 a6 a7 a8 n6 n7 n8 p)-(qOld c q6 q7 q8 a6 a7 a8 n6 n7 n8 p))) p
def cNew (c q6 q7 q8 a6 a7 a8 n6 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiNew c q6 q7 q8 a6 a7 a8 n6 n7 n8 p)-(qNew c q6 q7 q8 a6 a7 a8 n6 n7 n8 p))) p
theorem q_same (c q6 q7 q8 a6 a7 a8 n6 n7 n8 p : W) : qNew c q6 q7 q8 a6 a7 a8 n6 n7 n8 p = qOld c q6 q7 q8 a6 a7 a8 n6 n7 n8 p := by
  have h0 : (a6+a6)*a8 = a6*a8+a6*a8 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a6 a8
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, addA, addL, addC]
theorem c_same (c q6 q7 q8 a6 a7 a8 n6 n7 n8 p : W)
    (ha6 : a6.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q6 q7 q8 a6 a7 a8 n6 n7 n8 p = cOld c q6 q7 q8 a6 a7 a8 n6 n7 n8 p := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (p+((xs.foldr (fun x y => x+y) (N 0))-(qOld c q6 q7 q8 a6 a7 a8 n6 n7 n8 p))) p
  have hd : (qOld c q6 q7 q8 a6 a7 a8 n6 n7 n8 p).toNat < p.toNat := mask240_lt_p (loOld c q6 q7 q8 a6 a7 a8 n6 n7 n8 p)
  let ys0 : List W := [(UInt256.mulMod (q8) (n6) p), (UInt256.mulMod (q7) (n7) p), (UInt256.mulMod (q6) (n8) p), (UInt256.mulMod (a7) (a7) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_biased_list_radix240 a6 a8 (N 2048) (qOld c q6 q7 q8 a6 a7 a8 n6 n7 n8 p) ys0 ha6 (by simp [ys0]) hb0 hd
  have step0 : red [(UInt256.mulMod (q8) (n6) p), (UInt256.mulMod (q7) (n7) p), (UInt256.mulMod (q6) (n8) p), (UInt256.mulMod (a7) (a7) p), (UInt256.mulMod (a6+a6) (a8) p), c] = red [(UInt256.mulMod (q8) (n6) p), (UInt256.mulMod (q7) (n7) p), (UInt256.mulMod (q6) (n8) p), (UInt256.mulMod (a7) (a7) p), (UInt256.mulMod (a6) (a8) p), (UInt256.mulMod (a6) (a8) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using step0
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC14 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 6) (a 7) (a 8) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareD5 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareD5, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC14 inv a b n) (CycleSubmission.WordHistory.squareQ6 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 6) (a 7) (a 8) (n 6) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareC15 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC15, CycleSubmission.DirectRecovery.carry, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath14

namespace R9SharedMath15
open EvmSemantics Challenge.EvmProof.Word CycleSubmission.Prepared.Arithmetic R5SharedTools
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def loOld (c q7 q8 a7 a8 n7 n8 p : W) : W := ([((q8)*(n7)), ((q7)*(n8)), ((a7)*(a8)), ((a7)*(a8)), c].foldr (fun x y => x+y) (N 0))
def loNew (c q7 q8 a7 a8 n7 n8 p : W) : W := ([((q8)*(n7)), ((q7)*(n8)), ((a7+a7)*(a8)), c].foldr (fun x y => x+y) (N 0))
def hiOld (c q7 q8 a7 a8 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n7) p), (UInt256.mulMod (q7) (n8) p), (UInt256.mulMod (a7) (a8) p), (UInt256.mulMod (a7) (a8) p), c].foldr (fun x y => x+y) (N 0))
def hiNew (c q7 q8 a7 a8 n7 n8 p : W) : W := ([(UInt256.mulMod (q8) (n7) p), (UInt256.mulMod (q7) (n8) p), (UInt256.mulMod (a7+a7) (a8) p), c].foldr (fun x y => x+y) (N 0))
def qOld (c q7 q8 a7 a8 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loOld c q7 q8 a7 a8 n7 n8 p)
def qNew (c q7 q8 a7 a8 n7 n8 p : W) : W := UInt256.land (N (2^240-1)) (loNew c q7 q8 a7 a8 n7 n8 p)
def cOld (c q7 q8 a7 a8 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiOld c q7 q8 a7 a8 n7 n8 p)-(qOld c q7 q8 a7 a8 n7 n8 p))) p
def cNew (c q7 q8 a7 a8 n7 n8 p : W) : W := UInt256.mulMod (N 2048) (p+((hiNew c q7 q8 a7 a8 n7 n8 p)-(qNew c q7 q8 a7 a8 n7 n8 p))) p
theorem q_same (c q7 q8 a7 a8 n7 n8 p : W) : qNew c q7 q8 a7 a8 n7 n8 p = qOld c q7 q8 a7 a8 n7 n8 p := by
  have h0 : (a7+a7)*a8 = a7*a8+a7*a8 := by simpa only [mulC] using CycleSubmission.DoubleInput.low_double a7 a8
  simp only [qNew, qOld, loNew, loOld, List.foldr_cons, List.foldr_nil, word_add0, h0, addA, addL, addC]
theorem c_same (c q7 q8 a7 a8 n7 n8 p : W)
    (ha7 : a7.toNat < 2^240)
    (hp : p = CycleSubmission.WordArithmetic.P) (hc : c.toNat < p.toNat) :
    cNew c q7 q8 a7 a8 n7 n8 p = cOld c q7 q8 a7 a8 n7 n8 p := by
  subst p
  let p := CycleSubmission.WordArithmetic.P
  have hp0 : 0 < p.toNat := by
    dsimp only [p]
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  let red : List W → W := fun xs => UInt256.mulMod (N 2048) (p+((xs.foldr (fun x y => x+y) (N 0))-(qOld c q7 q8 a7 a8 n7 n8 p))) p
  have hd : (qOld c q7 q8 a7 a8 n7 n8 p).toNat < p.toNat := mask240_lt_p (loOld c q7 q8 a7 a8 n7 n8 p)
  let ys0 : List W := [(UInt256.mulMod (q8) (n7) p), (UInt256.mulMod (q7) (n8) p), c]
  have hb0 : ∀ x ∈ ys0, x.toNat ≤ p.toNat := by
    intro x hx
    simp [ys0] at hx
    rcases hx with rfl | rfl | rfl
    all_goals first
      | exact Nat.le_of_lt hc
      | exact Nat.le_of_lt (residue_lt _ _ _ hp0)
  have hh0 := high_double_biased_list_radix240 a7 a8 (N 2048) (qOld c q7 q8 a7 a8 n7 n8 p) ys0 ha7 (by simp [ys0]) hb0 hd
  have step0 : red [(UInt256.mulMod (q8) (n7) p), (UInt256.mulMod (q7) (n8) p), (UInt256.mulMod (a7+a7) (a8) p), c] = red [(UInt256.mulMod (q8) (n7) p), (UInt256.mulMod (q7) (n8) p), (UInt256.mulMod (a7) (a8) p), (UInt256.mulMod (a7) (a8) p), c] := by
    simpa only [red, ys0, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mmC] using hh0
  simpa only [cNew, cOld, hiNew, hiOld, q_same, red, List.foldr_cons, List.foldr_nil] using step0
theorem old_q_matches (inv : W) (a b n : Nat → W) : qOld (CycleSubmission.WordHistory.squareC15 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 7) (a 8) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareD6 inv a b n := by
  simp only [qOld, loOld, CycleSubmission.WordHistory.squareD6, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC]
theorem old_c_matches (inv : W) (a b n : Nat → W) : cOld (CycleSubmission.WordHistory.squareC15 inv a b n) (CycleSubmission.WordHistory.squareQ7 inv a b n) (CycleSubmission.WordHistory.squareQ8 inv a b n) (a 7) (a 8) (n 7) (n 8) CycleSubmission.WordArithmetic.P = CycleSubmission.WordHistory.squareC16 inv a b n := by
  simp only [cOld, hiOld, qOld, loOld, CycleSubmission.WordHistory.squareC16, CycleSubmission.DirectRecovery.carry, List.foldr_cons, List.foldr_nil, word_add0, mask240_literal, addA, addL, addC, mulC, mmC]
end R9SharedMath15
