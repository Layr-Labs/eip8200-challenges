import Challenge.Modexp.Submission.Proofs.R5.Words
import Challenge.Modexp.Submission.Proofs.R5.ExecProduct
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace CycleSubmission.R5.ProductCols
open EvmSemantics Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.ColumnExpressions
open HistoricalSearch.WordCancellation HistoricalSearch.ProductAccumulate
open CycleSubmission.WordArithmetic
open CycleSubmission.R5.ExecProduct

/-! ### pr column 0 (low) -/

def prE0 (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0 : UInt256) : Expr :=
  (Expr.product (x0) (b0))

theorem prE0_contract (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0 : UInt256) (ninv : UInt256) (N C : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_x0 : x0.toNat < radix) (h_b0 : b0.toNat < radix) (hC : C ≤ 18*(radix-1))
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (prCol0_o1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) = quotient (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) ninv ∧ (prCol0_o1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0).toNat < radix ∧
    (post (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) ninv n0).value % radix = 0 ∧
    (prCol0_o0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0).toNat = (post (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) ninv n0).value / radix ∧
    (prCol0_o0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0).toNat ≤ 18*(radix-1) := by
  have hq : (prCol0_o1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) = quotient (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) ninv := by
    show UInt256.shiftRight (inv * (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0).low) (UInt256.ofNat 16) = _
    rw [hinv]
    exact Words.quotient_shifted ninv _
  have hcar : (prCol0_o0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) = cancelledCarry (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) ninv n0 := by
    show UInt256.mulMod (UInt256.ofNat 2048) (UInt256.mulMod (UInt256.shiftRight
      (inv * (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0).low) (UInt256.ofNat 16)) n0 P + (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0).high P) P = _
    rw [hinv, hP]
    exact Words.low_carry _ ninv n0
  have hp : (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0).productsBounded ((radix-1)^2) := productBound x0 b0 radix h_x0 h_b0
  have hl : (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0).literalsBounded C := by simp [prE0, Expr.literalsBounded]
  have hv := valueBound (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) ((radix-1)^2) C hp hl
  have hpc : (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0).products ≤ 17 := by norm_num [prE0, Expr.products]
  have hlc : (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0).literals ≤ 1 := by norm_num [prE0, Expr.literals]
  have hpre : (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0).value ≤ 17*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 17*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  rw [hcar]
  refine ⟨hq, ?_⟩
  rw [hq]
  exact cancelled_contract _ ninv n0 N C (by norm_num [prE0, Expr.count]) hl hC hpre hn0 hN

/-! ### pr column 1 (low) -/

def prE1 (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0 : UInt256) : Expr :=
  (Expr.add (Expr.product (q0) (n1)) (Expr.add (Expr.product (x1) (b0)) (Expr.add (Expr.product (x0) (b1)) (Expr.literal (c)))))

theorem prE1_contract (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0 : UInt256) (ninv : UInt256) (N C : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q0 : q0.toNat < radix) (h_n1 : n1.toNat < radix) (h_x1 : x1.toNat < radix) (h_b0 : b0.toNat < radix) (h_x0 : x0.toNat < radix) (h_b1 : b1.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1))
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (prCol1_o1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) = quotient (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) ninv ∧ (prCol1_o1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0).toNat < radix ∧
    (post (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) ninv n0).value % radix = 0 ∧
    (prCol1_o0 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0).toNat = (post (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) ninv n0).value / radix ∧
    (prCol1_o0 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0).toNat ≤ 18*(radix-1) := by
  have hq : (prCol1_o1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) = quotient (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) ninv := by
    show UInt256.shiftRight (inv * (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0).low) (UInt256.ofNat 16) = _
    rw [hinv]
    exact Words.quotient_shifted ninv _
  have hcar : (prCol1_o0 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) = cancelledCarry (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) ninv n0 := by
    show UInt256.mulMod (UInt256.ofNat 2048) (UInt256.mulMod (UInt256.shiftRight
      (inv * (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0).low) (UInt256.ofNat 16)) n0 P + (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0).high P) P = _
    rw [hinv, hP]
    exact Words.low_carry _ ninv n0
  have hp : (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0).productsBounded ((radix-1)^2) := ⟨productBound q0 n1 radix h_q0 h_n1, ⟨productBound x1 b0 radix h_x1 h_b0, ⟨productBound x0 b1 radix h_x0 h_b1, True.intro⟩⟩⟩
  have hl : (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0).literalsBounded C := by simp [prE1, Expr.literalsBounded, hc]
  have hv := valueBound (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) ((radix-1)^2) C hp hl
  have hpc : (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0).products ≤ 17 := by norm_num [prE1, Expr.products]
  have hlc : (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0).literals ≤ 1 := by norm_num [prE1, Expr.literals]
  have hpre : (prE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0).value ≤ 17*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 17*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  rw [hcar]
  refine ⟨hq, ?_⟩
  rw [hq]
  exact cancelled_contract _ ninv n0 N C (by norm_num [prE1, Expr.count]) hl hC hpre hn0 hN

/-! ### pr column 2 (low) -/

def prE2 (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0 : UInt256) : Expr :=
  (Expr.add (Expr.product (q1) (n1)) (Expr.add (Expr.product (q0) (n2)) (Expr.add (Expr.product (x2) (b0)) (Expr.add (Expr.product (x1) (b1)) (Expr.add (Expr.product (x0) (b2)) (Expr.literal (c)))))))

theorem prE2_contract (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0 : UInt256) (ninv : UInt256) (N C : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q1 : q1.toNat < radix) (h_n1 : n1.toNat < radix) (h_q0 : q0.toNat < radix) (h_n2 : n2.toNat < radix) (h_x2 : x2.toNat < radix) (h_b0 : b0.toNat < radix) (h_x1 : x1.toNat < radix) (h_b1 : b1.toNat < radix) (h_x0 : x0.toNat < radix) (h_b2 : b2.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1))
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (prCol2_o1 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) = quotient (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) ninv ∧ (prCol2_o1 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0).toNat < radix ∧
    (post (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) ninv n0).value % radix = 0 ∧
    (prCol2_o0 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0).toNat = (post (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) ninv n0).value / radix ∧
    (prCol2_o0 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0).toNat ≤ 18*(radix-1) := by
  have hq : (prCol2_o1 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) = quotient (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) ninv := by
    show UInt256.shiftRight (inv * (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0).low) (UInt256.ofNat 16) = _
    rw [hinv]
    exact Words.quotient_shifted ninv _
  have hcar : (prCol2_o0 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) = cancelledCarry (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) ninv n0 := by
    show UInt256.mulMod (UInt256.ofNat 2048) (UInt256.mulMod (UInt256.shiftRight
      (inv * (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0).low) (UInt256.ofNat 16)) n0 P + (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0).high P) P = _
    rw [hinv, hP]
    exact Words.low_carry _ ninv n0
  have hp : (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0).productsBounded ((radix-1)^2) := ⟨productBound q1 n1 radix h_q1 h_n1, ⟨productBound q0 n2 radix h_q0 h_n2, ⟨productBound x2 b0 radix h_x2 h_b0, ⟨productBound x1 b1 radix h_x1 h_b1, ⟨productBound x0 b2 radix h_x0 h_b2, True.intro⟩⟩⟩⟩⟩
  have hl : (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0).literalsBounded C := by simp [prE2, Expr.literalsBounded, hc]
  have hv := valueBound (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) ((radix-1)^2) C hp hl
  have hpc : (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0).products ≤ 17 := by norm_num [prE2, Expr.products]
  have hlc : (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0).literals ≤ 1 := by norm_num [prE2, Expr.literals]
  have hpre : (prE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0).value ≤ 17*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 17*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  rw [hcar]
  refine ⟨hq, ?_⟩
  rw [hq]
  exact cancelled_contract _ ninv n0 N C (by norm_num [prE2, Expr.count]) hl hC hpre hn0 hN

/-! ### pr column 3 (low) -/

def prE3 (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0 : UInt256) : Expr :=
  (Expr.add (Expr.product (q2) (n1)) (Expr.add (Expr.product (q1) (n2)) (Expr.add (Expr.product (q0) (n3)) (Expr.add (Expr.product (x3) (b0)) (Expr.add (Expr.product (x2) (b1)) (Expr.add (Expr.product (x1) (b2)) (Expr.add (Expr.product (x0) (b3)) (Expr.literal (c)))))))))

theorem prE3_contract (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0 : UInt256) (ninv : UInt256) (N C : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q2 : q2.toNat < radix) (h_n1 : n1.toNat < radix) (h_q1 : q1.toNat < radix) (h_n2 : n2.toNat < radix) (h_q0 : q0.toNat < radix) (h_n3 : n3.toNat < radix) (h_x3 : x3.toNat < radix) (h_b0 : b0.toNat < radix) (h_x2 : x2.toNat < radix) (h_b1 : b1.toNat < radix) (h_x1 : x1.toNat < radix) (h_b2 : b2.toNat < radix) (h_x0 : x0.toNat < radix) (h_b3 : b3.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1))
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (prCol3_o1 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) = quotient (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) ninv ∧ (prCol3_o1 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0).toNat < radix ∧
    (post (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) ninv n0).value % radix = 0 ∧
    (prCol3_o0 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0).toNat = (post (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) ninv n0).value / radix ∧
    (prCol3_o0 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0).toNat ≤ 18*(radix-1) := by
  have hq : (prCol3_o1 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) = quotient (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) ninv := by
    show UInt256.shiftRight (inv * (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0).low) (UInt256.ofNat 16) = _
    rw [hinv]
    exact Words.quotient_shifted ninv _
  have hcar : (prCol3_o0 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) = cancelledCarry (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) ninv n0 := by
    show UInt256.mulMod (UInt256.ofNat 2048) (UInt256.mulMod (UInt256.shiftRight
      (inv * (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0).low) (UInt256.ofNat 16)) n0 P + (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0).high P) P = _
    rw [hinv, hP]
    exact Words.low_carry _ ninv n0
  have hp : (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0).productsBounded ((radix-1)^2) := ⟨productBound q2 n1 radix h_q2 h_n1, ⟨productBound q1 n2 radix h_q1 h_n2, ⟨productBound q0 n3 radix h_q0 h_n3, ⟨productBound x3 b0 radix h_x3 h_b0, ⟨productBound x2 b1 radix h_x2 h_b1, ⟨productBound x1 b2 radix h_x1 h_b2, ⟨productBound x0 b3 radix h_x0 h_b3, True.intro⟩⟩⟩⟩⟩⟩⟩
  have hl : (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0).literalsBounded C := by simp [prE3, Expr.literalsBounded, hc]
  have hv := valueBound (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) ((radix-1)^2) C hp hl
  have hpc : (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0).products ≤ 17 := by norm_num [prE3, Expr.products]
  have hlc : (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0).literals ≤ 1 := by norm_num [prE3, Expr.literals]
  have hpre : (prE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0).value ≤ 17*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 17*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  rw [hcar]
  refine ⟨hq, ?_⟩
  rw [hq]
  exact cancelled_contract _ ninv n0 N C (by norm_num [prE3, Expr.count]) hl hC hpre hn0 hN

/-! ### pr column 4 (low) -/

def prE4 (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 : UInt256) : Expr :=
  (Expr.add (Expr.product (q3) (n1)) (Expr.add (Expr.product (q2) (n2)) (Expr.add (Expr.product (q1) (n3)) (Expr.add (Expr.product (q0) (n4)) (Expr.add (Expr.product (x4) (b0)) (Expr.add (Expr.product (x3) (b1)) (Expr.add (Expr.product (x2) (b2)) (Expr.add (Expr.product (x1) (b3)) (Expr.add (Expr.product (x0) (b4)) (Expr.literal (c)))))))))))

theorem prE4_contract (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 : UInt256) (ninv : UInt256) (N C : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q3 : q3.toNat < radix) (h_n1 : n1.toNat < radix) (h_q2 : q2.toNat < radix) (h_n2 : n2.toNat < radix) (h_q1 : q1.toNat < radix) (h_n3 : n3.toNat < radix) (h_q0 : q0.toNat < radix) (h_n4 : n4.toNat < radix) (h_x4 : x4.toNat < radix) (h_b0 : b0.toNat < radix) (h_x3 : x3.toNat < radix) (h_b1 : b1.toNat < radix) (h_x2 : x2.toNat < radix) (h_b2 : b2.toNat < radix) (h_x1 : x1.toNat < radix) (h_b3 : b3.toNat < radix) (h_x0 : x0.toNat < radix) (h_b4 : b4.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1))
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (prCol4_o4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) = quotient (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) ninv ∧ (prCol4_o4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0).toNat < radix ∧
    (post (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) ninv n0).value % radix = 0 ∧
    (prCol4_o0 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0).toNat = (post (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) ninv n0).value / radix ∧
    (prCol4_o0 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0).toNat ≤ 18*(radix-1) := by
  have hq : (prCol4_o4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) = quotient (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) ninv := by
    show UInt256.shiftRight (inv * (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0).low) (UInt256.ofNat 16) = _
    rw [hinv]
    exact Words.quotient_shifted ninv _
  have hcar : (prCol4_o0 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) = cancelledCarry (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) ninv n0 := by
    show UInt256.mulMod (UInt256.ofNat 2048) (UInt256.mulMod (UInt256.shiftRight
      (inv * (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0).low) (UInt256.ofNat 16)) n0 P + (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0).high P) P = _
    rw [hinv, hP]
    exact Words.low_carry _ ninv n0
  have hp : (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0).productsBounded ((radix-1)^2) := ⟨productBound q3 n1 radix h_q3 h_n1, ⟨productBound q2 n2 radix h_q2 h_n2, ⟨productBound q1 n3 radix h_q1 h_n3, ⟨productBound q0 n4 radix h_q0 h_n4, ⟨productBound x4 b0 radix h_x4 h_b0, ⟨productBound x3 b1 radix h_x3 h_b1, ⟨productBound x2 b2 radix h_x2 h_b2, ⟨productBound x1 b3 radix h_x1 h_b3, ⟨productBound x0 b4 radix h_x0 h_b4, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0).literalsBounded C := by simp [prE4, Expr.literalsBounded, hc]
  have hv := valueBound (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) ((radix-1)^2) C hp hl
  have hpc : (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0).products ≤ 17 := by norm_num [prE4, Expr.products]
  have hlc : (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0).literals ≤ 1 := by norm_num [prE4, Expr.literals]
  have hpre : (prE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0).value ≤ 17*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 17*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  rw [hcar]
  refine ⟨hq, ?_⟩
  rw [hq]
  exact cancelled_contract _ ninv n0 N C (by norm_num [prE4, Expr.count]) hl hC hpre hn0 hN

/-! ### pr column 5 (high) -/

def prE5 (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M : UInt256) : Expr :=
  (Expr.add (Expr.product (q4) (n1)) (Expr.add (Expr.product (q3) (n2)) (Expr.add (Expr.product (q2) (n3)) (Expr.add (Expr.product (q1) (n4)) (Expr.add (Expr.product (x4) (b1)) (Expr.add (Expr.product (x3) (b2)) (Expr.add (Expr.product (x2) (b3)) (Expr.add (Expr.product (x1) (b4)) (Expr.literal (c))))))))))

theorem prE5_digit (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M : UInt256) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prCol5_o5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).toNat = (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).value % radix := by
  show (UInt256.land M (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).low).toNat = _
  rw [hM]
  exact digitValue _

theorem prE5_contract (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M : UInt256) (C : Nat) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q4 : q4.toNat < radix) (h_n1 : n1.toNat < radix) (h_q3 : q3.toNat < radix) (h_n2 : n2.toNat < radix) (h_q2 : q2.toNat < radix) (h_n3 : n3.toNat < radix) (h_q1 : q1.toNat < radix) (h_n4 : n4.toNat < radix) (h_x4 : x4.toNat < radix) (h_b1 : b1.toNat < radix) (h_x3 : x3.toNat < radix) (h_b2 : b2.toNat < radix) (h_x2 : x2.toNat < radix) (h_b3 : b3.toNat < radix) (h_x1 : x1.toNat < radix) (h_b4 : b4.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1)) :
    (prCol5_o0 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).toNat = (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).value / radix ∧ (prCol5_o0 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).toNat ≤ 18*(radix-1) := by
  have hcar : (prCol5_o0 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M) = HistoricalSearch.RoundedWordBridge.carryWord ((prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).high CycleSubmission.WordArithmetic.P)
      (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).low CycleSubmission.WordArithmetic.P (UInt256.ofNat 240) (UInt256.ofNat 16) := by
    show UInt256.shiftRight (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).low (UInt256.ofNat 240) + UInt256.shiftLeft (UInt256.shiftRight
      (UInt256.addMod (UInt256.lnot (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).low) ((prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).high P) P) (UInt256.ofNat 5)) (UInt256.ofNat 16) = _
    rw [hP]
    exact Words.high_carry _ _
  have hp : (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).productsBounded ((radix-1)^2) := ⟨productBound q4 n1 radix h_q4 h_n1, ⟨productBound q3 n2 radix h_q3 h_n2, ⟨productBound q2 n3 radix h_q2 h_n3, ⟨productBound q1 n4 radix h_q1 h_n4, ⟨productBound x4 b1 radix h_x4 h_b1, ⟨productBound x3 b2 radix h_x3 h_b2, ⟨productBound x2 b3 radix h_x2 h_b3, ⟨productBound x1 b4 radix h_x1 h_b4, True.intro⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).literalsBounded C := by simp [prE5, Expr.literalsBounded, hc]
  have hv := valueBound (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M) ((radix-1)^2) C hp hl
  have hpc : (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).products ≤ 18 := by norm_num [prE5, Expr.products]
  have hlc : (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).literals ≤ 1 := by norm_num [prE5, Expr.literals]
  have hs : (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).value ≤ 18*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 18*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  have hCP : C ≤ residueModulus-1 := by
    norm_num [radix, residueModulus] at hC ⊢
    omega
  have hlP : (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).literalsBounded (residueModulus-1) := by simp [prE5, Expr.literalsBounded, le_trans hc hCP]
  have hh := highInvariant CycleSubmission.WordArithmetic.P pValue (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M) (by norm_num [prE5, Expr.count]) hlP
  have hr := rounded_contract ((prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).high CycleSubmission.WordArithmetic.P) (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).low (prE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).value C hC hs
    (lowValue _) hh.2
  rw [hcar]
  refine ⟨hr, ?_⟩
  rw [hr]
  exact (CycleSubmission.Bounds.fullColumnBounds _ C hC hs).1

/-! ### pr column 6 (high) -/

def prE6 (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M : UInt256) : Expr :=
  (Expr.add (Expr.product (q4) (n2)) (Expr.add (Expr.product (q3) (n3)) (Expr.add (Expr.product (q2) (n4)) (Expr.add (Expr.product (x4) (b2)) (Expr.add (Expr.product (x3) (b3)) (Expr.add (Expr.product (x2) (b4)) (Expr.literal (c))))))))

theorem prE6_digit (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M : UInt256) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prCol6_o6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).toNat = (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).value % radix := by
  show (UInt256.land M (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).low).toNat = _
  rw [hM]
  exact digitValue _

theorem prE6_contract (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M : UInt256) (C : Nat) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q4 : q4.toNat < radix) (h_n2 : n2.toNat < radix) (h_q3 : q3.toNat < radix) (h_n3 : n3.toNat < radix) (h_q2 : q2.toNat < radix) (h_n4 : n4.toNat < radix) (h_x4 : x4.toNat < radix) (h_b2 : b2.toNat < radix) (h_x3 : x3.toNat < radix) (h_b3 : b3.toNat < radix) (h_x2 : x2.toNat < radix) (h_b4 : b4.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1)) :
    (prCol6_o0 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).toNat = (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).value / radix ∧ (prCol6_o0 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).toNat ≤ 18*(radix-1) := by
  have hcar : (prCol6_o0 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M) = HistoricalSearch.RoundedWordBridge.carryWord ((prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).high CycleSubmission.WordArithmetic.P)
      (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).low CycleSubmission.WordArithmetic.P (UInt256.ofNat 240) (UInt256.ofNat 16) := by
    show UInt256.shiftRight (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).low (UInt256.ofNat 240) + UInt256.shiftLeft (UInt256.shiftRight
      (UInt256.addMod (UInt256.lnot (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).low) ((prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).high P) P) (UInt256.ofNat 5)) (UInt256.ofNat 16) = _
    rw [hP]
    exact Words.high_carry _ _
  have hp : (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).productsBounded ((radix-1)^2) := ⟨productBound q4 n2 radix h_q4 h_n2, ⟨productBound q3 n3 radix h_q3 h_n3, ⟨productBound q2 n4 radix h_q2 h_n4, ⟨productBound x4 b2 radix h_x4 h_b2, ⟨productBound x3 b3 radix h_x3 h_b3, ⟨productBound x2 b4 radix h_x2 h_b4, True.intro⟩⟩⟩⟩⟩⟩
  have hl : (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).literalsBounded C := by simp [prE6, Expr.literalsBounded, hc]
  have hv := valueBound (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M) ((radix-1)^2) C hp hl
  have hpc : (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).products ≤ 18 := by norm_num [prE6, Expr.products]
  have hlc : (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).literals ≤ 1 := by norm_num [prE6, Expr.literals]
  have hs : (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).value ≤ 18*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 18*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  have hCP : C ≤ residueModulus-1 := by
    norm_num [radix, residueModulus] at hC ⊢
    omega
  have hlP : (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).literalsBounded (residueModulus-1) := by simp [prE6, Expr.literalsBounded, le_trans hc hCP]
  have hh := highInvariant CycleSubmission.WordArithmetic.P pValue (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M) (by norm_num [prE6, Expr.count]) hlP
  have hr := rounded_contract ((prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).high CycleSubmission.WordArithmetic.P) (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).low (prE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).value C hC hs
    (lowValue _) hh.2
  rw [hcar]
  refine ⟨hr, ?_⟩
  rw [hr]
  exact (CycleSubmission.Bounds.fullColumnBounds _ C hC hs).1

/-! ### pr column 7 (high) -/

def prE7 (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M : UInt256) : Expr :=
  (Expr.add (Expr.product (q4) (n3)) (Expr.add (Expr.product (q3) (n4)) (Expr.add (Expr.product (x4) (b3)) (Expr.add (Expr.product (x3) (b4)) (Expr.literal (c))))))

theorem prE7_digit (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M : UInt256) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prCol7_o7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).toNat = (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).value % radix := by
  show (UInt256.land M (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).low).toNat = _
  rw [hM]
  exact digitValue _

theorem prE7_contract (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M : UInt256) (C : Nat) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q4 : q4.toNat < radix) (h_n3 : n3.toNat < radix) (h_q3 : q3.toNat < radix) (h_n4 : n4.toNat < radix) (h_x4 : x4.toNat < radix) (h_b3 : b3.toNat < radix) (h_x3 : x3.toNat < radix) (h_b4 : b4.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1)) :
    (prCol7_o0 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).toNat = (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).value / radix ∧ (prCol7_o0 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).toNat ≤ 18*(radix-1) := by
  have hcar : (prCol7_o0 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M) = HistoricalSearch.RoundedWordBridge.carryWord ((prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).high CycleSubmission.WordArithmetic.P)
      (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).low CycleSubmission.WordArithmetic.P (UInt256.ofNat 240) (UInt256.ofNat 16) := by
    show UInt256.shiftRight (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).low (UInt256.ofNat 240) + UInt256.shiftLeft (UInt256.shiftRight
      (UInt256.addMod (UInt256.lnot (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).low) ((prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).high P) P) (UInt256.ofNat 5)) (UInt256.ofNat 16) = _
    rw [hP]
    exact Words.high_carry _ _
  have hp : (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).productsBounded ((radix-1)^2) := ⟨productBound q4 n3 radix h_q4 h_n3, ⟨productBound q3 n4 radix h_q3 h_n4, ⟨productBound x4 b3 radix h_x4 h_b3, ⟨productBound x3 b4 radix h_x3 h_b4, True.intro⟩⟩⟩⟩
  have hl : (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).literalsBounded C := by simp [prE7, Expr.literalsBounded, hc]
  have hv := valueBound (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M) ((radix-1)^2) C hp hl
  have hpc : (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).products ≤ 18 := by norm_num [prE7, Expr.products]
  have hlc : (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).literals ≤ 1 := by norm_num [prE7, Expr.literals]
  have hs : (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).value ≤ 18*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 18*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  have hCP : C ≤ residueModulus-1 := by
    norm_num [radix, residueModulus] at hC ⊢
    omega
  have hlP : (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).literalsBounded (residueModulus-1) := by simp [prE7, Expr.literalsBounded, le_trans hc hCP]
  have hh := highInvariant CycleSubmission.WordArithmetic.P pValue (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M) (by norm_num [prE7, Expr.count]) hlP
  have hr := rounded_contract ((prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).high CycleSubmission.WordArithmetic.P) (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).low (prE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).value C hC hs
    (lowValue _) hh.2
  rw [hcar]
  refine ⟨hr, ?_⟩
  rw [hr]
  exact (CycleSubmission.Bounds.fullColumnBounds _ C hC hs).1

/-! ### pr column 8 (high) -/

def prE8 (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M : UInt256) : Expr :=
  (Expr.add (Expr.product (q4) (n4)) (Expr.add (Expr.product (x4) (b4)) (Expr.literal (c))))

theorem prE8_digit (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M : UInt256) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prCol8_o8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).toNat = (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).value % radix := by
  show (UInt256.land M (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).low).toNat = _
  rw [hM]
  exact digitValue _

theorem prE8_contract (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M : UInt256) (C : Nat) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q4 : q4.toNat < radix) (h_n4 : n4.toNat < radix) (h_x4 : x4.toNat < radix) (h_b4 : b4.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1)) :
    (prCol8_o0 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).toNat = (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).value / radix ∧ (prCol8_o0 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).toNat ≤ 18*(radix-1) := by
  have hcar : (prCol8_o0 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M) = HistoricalSearch.RoundedWordBridge.carryWord ((prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).high CycleSubmission.WordArithmetic.P)
      (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).low CycleSubmission.WordArithmetic.P (UInt256.ofNat 240) (UInt256.ofNat 16) := by
    show UInt256.shiftRight (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).low (UInt256.ofNat 240) + UInt256.shiftLeft (UInt256.shiftRight
      (UInt256.addMod (UInt256.lnot (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).low) ((prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).high P) P) (UInt256.ofNat 5)) (UInt256.ofNat 16) = _
    rw [hP]
    exact Words.high_carry _ _
  have hp : (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).productsBounded ((radix-1)^2) := ⟨productBound q4 n4 radix h_q4 h_n4, ⟨productBound x4 b4 radix h_x4 h_b4, True.intro⟩⟩
  have hl : (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).literalsBounded C := by simp [prE8, Expr.literalsBounded, hc]
  have hv := valueBound (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M) ((radix-1)^2) C hp hl
  have hpc : (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).products ≤ 18 := by norm_num [prE8, Expr.products]
  have hlc : (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).literals ≤ 1 := by norm_num [prE8, Expr.literals]
  have hs : (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).value ≤ 18*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 18*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  have hCP : C ≤ residueModulus-1 := by
    norm_num [radix, residueModulus] at hC ⊢
    omega
  have hlP : (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).literalsBounded (residueModulus-1) := by simp [prE8, Expr.literalsBounded, le_trans hc hCP]
  have hh := highInvariant CycleSubmission.WordArithmetic.P pValue (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M) (by norm_num [prE8, Expr.count]) hlP
  have hr := rounded_contract ((prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).high CycleSubmission.WordArithmetic.P) (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).low (prE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cntp b4 M).value C hC hs
    (lowValue _) hh.2
  rw [hcar]
  refine ⟨hr, ?_⟩
  rw [hr]
  exact (CycleSubmission.Bounds.fullColumnBounds _ C hC hs).1

end CycleSubmission.R5.ProductCols
