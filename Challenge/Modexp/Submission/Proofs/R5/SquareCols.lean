import Challenge.Modexp.Submission.Proofs.Cycle.DirectRecovery
import Challenge.Modexp.Submission.Proofs.R5.Words
import Challenge.Modexp.Submission.Proofs.R5.ExecSquare
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace CycleSubmission.R5.SquareCols
open EvmSemantics Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.ColumnExpressions
open HistoricalSearch.WordCancellation HistoricalSearch.ProductAccumulate
open CycleSubmission.WordArithmetic
open CycleSubmission.R5.ExecSquare

/-! ### sq column 0 (low) -/

def sqE0 (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : Expr :=
  (Expr.product (a0) (a0))

theorem sqE0_contract (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N C : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_a0 : a0.toNat < radix) (hC : C ≤ 18*(radix-1))
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqCol0_o1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv ∧ (sqCol0_o1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat < radix ∧
    (post (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value % radix = 0 ∧
    (sqCol0_o0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (post (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value / radix ∧
    (sqCol0_o0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have hq : (sqCol0_o1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv := by
    show UInt256.shiftRight (inv * (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).low) (UInt256.ofNat 16) = _
    rw [hinv]
    exact Words.quotient_shifted ninv _
  have hcar : (sqCol0_o0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) = cancelledCarry (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0 := by
    show UInt256.mulMod (UInt256.ofNat 2048) (UInt256.mulMod (UInt256.shiftRight
      (inv * (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).low) (UInt256.ofNat 16)) n0 P + (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).high P) P = _
    rw [hinv, hP]
    exact Words.low_carry _ ninv n0
  have hp : (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).productsBounded ((radix-1)^2) := productBound a0 a0 radix h_a0 h_a0
  have hl : (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).literalsBounded C := by simp [sqE0, Expr.literalsBounded]
  have hv := valueBound (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ((radix-1)^2) C hp hl
  have hpc : (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).products ≤ 17 := by norm_num [sqE0, Expr.products]
  have hlc : (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).literals ≤ 1 := by norm_num [sqE0, Expr.literals]
  have hpre : (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).value ≤ 17*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 17*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  rw [hcar]
  refine ⟨hq, ?_⟩
  rw [hq]
  exact cancelled_contract _ ninv n0 N C (by norm_num [sqE0, Expr.count]) hl hC hpre hn0 hN

/-! ### sq column 1 (low) -/

def sqE1 (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : Expr :=
  (Expr.add (Expr.product (q0) (n1)) (Expr.add (Expr.add (Expr.product (x0) (x1)) (Expr.product (x0) (x1))) (Expr.literal (c))))

theorem sqE1_contract (c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N C : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q0 : q0.toNat < radix) (h_n1 : n1.toNat < radix) (h_x0 : x0.toNat < radix) (h_x1 : x1.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1))
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqCol1_o1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv ∧ (sqCol1_o1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).toNat < radix ∧
    (post (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value % radix = 0 ∧
    (sqCol1_o0 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).toNat = (post (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value / radix ∧
    (sqCol1_o0 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have hq : (sqCol1_o1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv := by
    show UInt256.shiftRight (inv * (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).low) (UInt256.ofNat 16) = _
    rw [hinv]
    exact Words.quotient_shifted ninv _
  have hcar : (sqCol1_o0 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) = cancelledCarry (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv n0 := by
    show UInt256.mulMod (UInt256.ofNat 2048) (UInt256.mulMod (UInt256.shiftRight
      (inv * (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).low) (UInt256.ofNat 16)) n0 P + (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).high P) P = _
    rw [hinv, hP]
    exact Words.low_carry _ ninv n0
  have hp : (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).productsBounded ((radix-1)^2) := ⟨productBound q0 n1 radix h_q0 h_n1, ⟨⟨productBound x0 x1 radix h_x0 h_x1, productBound x0 x1 radix h_x0 h_x1⟩, True.intro⟩⟩
  have hl : (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).literalsBounded C := by simp [sqE1, Expr.literalsBounded, hc]
  have hv := valueBound (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ((radix-1)^2) C hp hl
  have hpc : (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).products ≤ 17 := by norm_num [sqE1, Expr.products]
  have hlc : (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).literals ≤ 1 := by norm_num [sqE1, Expr.literals]
  have hpre : (sqE1 c q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).value ≤ 17*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 17*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  rw [hcar]
  refine ⟨hq, ?_⟩
  rw [hq]
  exact cancelled_contract _ ninv n0 N C (by norm_num [sqE1, Expr.count]) hl hC hpre hn0 hN

/-! ### sq column 2 (low) -/

def sqE2 (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : Expr :=
  (Expr.add (Expr.product (q1) (n1)) (Expr.add (Expr.product (q0) (n2)) (Expr.add (Expr.product (x1) (x1)) (Expr.add (Expr.add (Expr.product (x0) (x2)) (Expr.product (x0) (x2))) (Expr.literal (c))))))

theorem sqE2_contract (c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N C : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q1 : q1.toNat < radix) (h_n1 : n1.toNat < radix) (h_q0 : q0.toNat < radix) (h_n2 : n2.toNat < radix) (h_x1 : x1.toNat < radix) (h_x0 : x0.toNat < radix) (h_x2 : x2.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1))
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqCol2_o1 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv ∧ (sqCol2_o1 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).toNat < radix ∧
    (post (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value % radix = 0 ∧
    (sqCol2_o0 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).toNat = (post (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value / radix ∧
    (sqCol2_o0 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have hq : (sqCol2_o1 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv := by
    show UInt256.shiftRight (inv * (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).low) (UInt256.ofNat 16) = _
    rw [hinv]
    exact Words.quotient_shifted ninv _
  have hcar : (sqCol2_o0 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) = cancelledCarry (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv n0 := by
    show UInt256.mulMod (UInt256.ofNat 2048) (UInt256.mulMod (UInt256.shiftRight
      (inv * (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).low) (UInt256.ofNat 16)) n0 P + (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).high P) P = _
    rw [hinv, hP]
    exact Words.low_carry _ ninv n0
  have hp : (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).productsBounded ((radix-1)^2) := ⟨productBound q1 n1 radix h_q1 h_n1, ⟨productBound q0 n2 radix h_q0 h_n2, ⟨productBound x1 x1 radix h_x1 h_x1, ⟨⟨productBound x0 x2 radix h_x0 h_x2, productBound x0 x2 radix h_x0 h_x2⟩, True.intro⟩⟩⟩⟩
  have hl : (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).literalsBounded C := by simp [sqE2, Expr.literalsBounded, hc]
  have hv := valueBound (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ((radix-1)^2) C hp hl
  have hpc : (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).products ≤ 17 := by norm_num [sqE2, Expr.products]
  have hlc : (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).literals ≤ 1 := by norm_num [sqE2, Expr.literals]
  have hpre : (sqE2 c q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).value ≤ 17*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 17*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  rw [hcar]
  refine ⟨hq, ?_⟩
  rw [hq]
  exact cancelled_contract _ ninv n0 N C (by norm_num [sqE2, Expr.count]) hl hC hpre hn0 hN

/-! ### sq column 3 (low) -/

def sqE3 (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : Expr :=
  (Expr.add (Expr.product (q2) (n1)) (Expr.add (Expr.product (q1) (n2)) (Expr.add (Expr.product (q0) (n3)) (Expr.add (Expr.add (Expr.add (Expr.product (x1) (x2)) (Expr.product (x0) (x3))) (Expr.add (Expr.product (x1) (x2)) (Expr.product (x0) (x3)))) (Expr.literal (c))))))

theorem sqE3_contract (c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N C : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q2 : q2.toNat < radix) (h_n1 : n1.toNat < radix) (h_q1 : q1.toNat < radix) (h_n2 : n2.toNat < radix) (h_q0 : q0.toNat < radix) (h_n3 : n3.toNat < radix) (h_x1 : x1.toNat < radix) (h_x2 : x2.toNat < radix) (h_x0 : x0.toNat < radix) (h_x3 : x3.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1))
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqCol3_o1 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv ∧ (sqCol3_o1 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).toNat < radix ∧
    (post (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value % radix = 0 ∧
    (sqCol3_o0 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).toNat = (post (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value / radix ∧
    (sqCol3_o0 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have hq : (sqCol3_o1 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv := by
    show UInt256.shiftRight (inv * (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).low) (UInt256.ofNat 16) = _
    rw [hinv]
    exact Words.quotient_shifted ninv _
  have hcar : (sqCol3_o0 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) = cancelledCarry (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv n0 := by
    show UInt256.mulMod (UInt256.ofNat 2048) (UInt256.mulMod (UInt256.shiftRight
      (inv * (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).low) (UInt256.ofNat 16)) n0 P + (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).high P) P = _
    rw [hinv, hP]
    exact Words.low_carry _ ninv n0
  have hp : (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).productsBounded ((radix-1)^2) := ⟨productBound q2 n1 radix h_q2 h_n1, ⟨productBound q1 n2 radix h_q1 h_n2, ⟨productBound q0 n3 radix h_q0 h_n3, ⟨⟨⟨productBound x1 x2 radix h_x1 h_x2, productBound x0 x3 radix h_x0 h_x3⟩, ⟨productBound x1 x2 radix h_x1 h_x2, productBound x0 x3 radix h_x0 h_x3⟩⟩, True.intro⟩⟩⟩⟩
  have hl : (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).literalsBounded C := by simp [sqE3, Expr.literalsBounded, hc]
  have hv := valueBound (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ((radix-1)^2) C hp hl
  have hpc : (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).products ≤ 17 := by norm_num [sqE3, Expr.products]
  have hlc : (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).literals ≤ 1 := by norm_num [sqE3, Expr.literals]
  have hpre : (sqE3 c q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).value ≤ 17*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 17*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  rw [hcar]
  refine ⟨hq, ?_⟩
  rw [hq]
  exact cancelled_contract _ ninv n0 N C (by norm_num [sqE3, Expr.count]) hl hC hpre hn0 hN

/-! ### sq column 4 (low) -/

def sqE4 (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : Expr :=
  (Expr.add (Expr.product (q3) (n1)) (Expr.add (Expr.product (q2) (n2)) (Expr.add (Expr.product (q1) (n3)) (Expr.add (Expr.product (q0) (n4)) (Expr.add (Expr.product (x2) (x2)) (Expr.add (Expr.add (Expr.product (x1) (x3)) (Expr.product (x1) (x3))) (Expr.add (Expr.add (Expr.product (x0) (x4)) (Expr.product (x0) (x4))) (Expr.literal (c)))))))))

theorem sqE4_contract (c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N C : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q3 : q3.toNat < radix) (h_n1 : n1.toNat < radix) (h_q2 : q2.toNat < radix) (h_n2 : n2.toNat < radix) (h_q1 : q1.toNat < radix) (h_n3 : n3.toNat < radix) (h_q0 : q0.toNat < radix) (h_n4 : n4.toNat < radix) (h_x2 : x2.toNat < radix) (h_x1 : x1.toNat < radix) (h_x3 : x3.toNat < radix) (h_x0 : x0.toNat < radix) (h_x4 : x4.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1))
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqCol4_o4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv ∧ (sqCol4_o4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).toNat < radix ∧
    (post (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value % radix = 0 ∧
    (sqCol4_o0 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).toNat = (post (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value / radix ∧
    (sqCol4_o0 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have hq : (sqCol4_o4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv := by
    show UInt256.shiftRight (inv * (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).low) (UInt256.ofNat 16) = _
    rw [hinv]
    exact Words.quotient_shifted ninv _
  have hcar : (sqCol4_o0 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) = cancelledCarry (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ninv n0 := by
    show UInt256.mulMod (UInt256.ofNat 2048) (UInt256.mulMod (UInt256.shiftRight
      (inv * (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).low) (UInt256.ofNat 16)) n0 P + (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).high P) P = _
    rw [hinv, hP]
    exact Words.low_carry _ ninv n0
  have hp : (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).productsBounded ((radix-1)^2) := ⟨productBound q3 n1 radix h_q3 h_n1, ⟨productBound q2 n2 radix h_q2 h_n2, ⟨productBound q1 n3 radix h_q1 h_n3, ⟨productBound q0 n4 radix h_q0 h_n4, ⟨productBound x2 x2 radix h_x2 h_x2, ⟨⟨productBound x1 x3 radix h_x1 h_x3, productBound x1 x3 radix h_x1 h_x3⟩, ⟨⟨productBound x0 x4 radix h_x0 h_x4, productBound x0 x4 radix h_x0 h_x4⟩, True.intro⟩⟩⟩⟩⟩⟩⟩
  have hl : (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).literalsBounded C := by simp [sqE4, Expr.literalsBounded, hc]
  have hv := valueBound (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0) ((radix-1)^2) C hp hl
  have hpc : (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).products ≤ 17 := by norm_num [sqE4, Expr.products]
  have hlc : (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).literals ≤ 1 := by norm_num [sqE4, Expr.literals]
  have hpre : (sqE4 c q3 q2 q1 q0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt n0).value ≤ 17*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 17*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  rw [hcar]
  refine ⟨hq, ?_⟩
  rw [hq]
  exact cancelled_contract _ ninv n0 N C (by norm_num [sqE4, Expr.count]) hl hC hpre hn0 hN

/-! ### sq column 5 (high) -/

def sqE5 (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : Expr :=
  (Expr.add (Expr.product (q4) (n1)) (Expr.add (Expr.product (q3) (n2)) (Expr.add (Expr.product (q2) (n3)) (Expr.add (Expr.product (q1) (n4)) (Expr.add (Expr.add (Expr.product (x2) (x3)) (Expr.product (x2) (x3))) (Expr.add (Expr.add (Expr.product (x1) (x4)) (Expr.product (x1) (x4))) (Expr.literal (c))))))))

theorem sqE5_digit (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) :
    (sqCol5_o5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).toNat = (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).value % radix := by
  show (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).low).toNat = _
  rw [Words.mask_literal]
  exact digitValue _

theorem sqE5_contract (c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (C : Nat) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q4 : q4.toNat < radix) (h_n1 : n1.toNat < radix) (h_q3 : q3.toNat < radix) (h_n2 : n2.toNat < radix) (h_q2 : q2.toNat < radix) (h_n3 : n3.toNat < radix) (h_q1 : q1.toNat < radix) (h_n4 : n4.toNat < radix) (h_x2 : x2.toNat < radix) (h_x3 : x3.toNat < radix) (h_x1 : x1.toNat < radix) (h_x4 : x4.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1)) :
    (sqCol5_o0 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).toNat = (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).value / radix ∧ (sqCol5_o0 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).toNat ≤ 18*(radix-1) := by
  have hcar : (sqCol5_o0 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) = CycleSubmission.DirectRecovery.carry ((sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).high CycleSubmission.WordArithmetic.P) (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).low := by
    show UInt256.mulMod (P + ((sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).high P - UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).low)) (UInt256.ofNat 2048) P = _
    rw [hP]
    rfl
  have hp : (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).productsBounded ((radix-1)^2) := ⟨productBound q4 n1 radix h_q4 h_n1, ⟨productBound q3 n2 radix h_q3 h_n2, ⟨productBound q2 n3 radix h_q2 h_n3, ⟨productBound q1 n4 radix h_q1 h_n4, ⟨⟨productBound x2 x3 radix h_x2 h_x3, productBound x2 x3 radix h_x2 h_x3⟩, ⟨⟨productBound x1 x4 radix h_x1 h_x4, productBound x1 x4 radix h_x1 h_x4⟩, True.intro⟩⟩⟩⟩⟩⟩
  have hl : (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).literalsBounded C := by simp [sqE5, Expr.literalsBounded, hc]
  have hv := valueBound (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) ((radix-1)^2) C hp hl
  have hpc : (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).products ≤ 18 := by norm_num [sqE5, Expr.products]
  have hlc : (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).literals ≤ 1 := by norm_num [sqE5, Expr.literals]
  have hs : (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).value ≤ 18*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 18*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  have hCP : C ≤ residueModulus-1 := by
    norm_num [radix, residueModulus] at hC ⊢
    omega
  have hlP : (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).literalsBounded (residueModulus-1) := by simp [sqE5, Expr.literalsBounded, le_trans hc hCP]
  have hr := CycleSubmission.DirectRecovery.expression_contract (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) (sqE5 c q3 q2 q1 q4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) C
    (by norm_num [sqE5, Expr.count]) hlP rfl hC hs
  rw [hcar]
  refine ⟨hr, ?_⟩
  rw [hr]
  exact (CycleSubmission.Bounds.fullColumnBounds _ C hC hs).1

/-! ### sq column 6 (high) -/

def sqE6 (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : Expr :=
  (Expr.add (Expr.product (q4) (n2)) (Expr.add (Expr.product (q3) (n3)) (Expr.add (Expr.product (q2) (n4)) (Expr.add (Expr.product (x3) (x3)) (Expr.add (Expr.add (Expr.product (x2) (x4)) (Expr.product (x2) (x4))) (Expr.literal (c)))))))

theorem sqE6_digit (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) :
    (sqCol6_o6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).toNat = (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).value % radix := by
  show (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).low).toNat = _
  rw [Words.mask_literal]
  exact digitValue _

theorem sqE6_contract (c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (C : Nat) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q4 : q4.toNat < radix) (h_n2 : n2.toNat < radix) (h_q3 : q3.toNat < radix) (h_n3 : n3.toNat < radix) (h_q2 : q2.toNat < radix) (h_n4 : n4.toNat < radix) (h_x3 : x3.toNat < radix) (h_x2 : x2.toNat < radix) (h_x4 : x4.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1)) :
    (sqCol6_o0 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).toNat = (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).value / radix ∧ (sqCol6_o0 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).toNat ≤ 18*(radix-1) := by
  have hcar : (sqCol6_o0 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) = CycleSubmission.DirectRecovery.carry ((sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).high CycleSubmission.WordArithmetic.P) (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).low := by
    show UInt256.mulMod (P + ((sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).high P - UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).low)) (UInt256.ofNat 2048) P = _
    rw [hP]
    rfl
  have hp : (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).productsBounded ((radix-1)^2) := ⟨productBound q4 n2 radix h_q4 h_n2, ⟨productBound q3 n3 radix h_q3 h_n3, ⟨productBound q2 n4 radix h_q2 h_n4, ⟨productBound x3 x3 radix h_x3 h_x3, ⟨⟨productBound x2 x4 radix h_x2 h_x4, productBound x2 x4 radix h_x2 h_x4⟩, True.intro⟩⟩⟩⟩⟩
  have hl : (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).literalsBounded C := by simp [sqE6, Expr.literalsBounded, hc]
  have hv := valueBound (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) ((radix-1)^2) C hp hl
  have hpc : (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).products ≤ 18 := by norm_num [sqE6, Expr.products]
  have hlc : (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).literals ≤ 1 := by norm_num [sqE6, Expr.literals]
  have hs : (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).value ≤ 18*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 18*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  have hCP : C ≤ residueModulus-1 := by
    norm_num [radix, residueModulus] at hC ⊢
    omega
  have hlP : (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).literalsBounded (residueModulus-1) := by simp [sqE6, Expr.literalsBounded, le_trans hc hCP]
  have hr := CycleSubmission.DirectRecovery.expression_contract (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) (sqE6 c q3 q2 q1 q4 z0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) C
    (by norm_num [sqE6, Expr.count]) hlP rfl hC hs
  rw [hcar]
  refine ⟨hr, ?_⟩
  rw [hr]
  exact (CycleSubmission.Bounds.fullColumnBounds _ C hC hs).1

/-! ### sq column 7 (high) -/

def sqE7 (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : Expr :=
  (Expr.add (Expr.product (q4) (n3)) (Expr.add (Expr.product (q3) (n4)) (Expr.add (Expr.add (Expr.product (x3) (x4)) (Expr.product (x3) (x4))) (Expr.literal (c)))))

theorem sqE7_digit (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) :
    (sqCol7_o7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).toNat = (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).value % radix := by
  show (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).low).toNat = _
  rw [Words.mask_literal]
  exact digitValue _

theorem sqE7_contract (c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (C : Nat) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q4 : q4.toNat < radix) (h_n3 : n3.toNat < radix) (h_q3 : q3.toNat < radix) (h_n4 : n4.toNat < radix) (h_x3 : x3.toNat < radix) (h_x4 : x4.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1)) :
    (sqCol7_o0 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).toNat = (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).value / radix ∧ (sqCol7_o0 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).toNat ≤ 18*(radix-1) := by
  have hcar : (sqCol7_o0 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) = CycleSubmission.DirectRecovery.carry ((sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).high CycleSubmission.WordArithmetic.P) (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).low := by
    show UInt256.mulMod (P + ((sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).high P - UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).low)) (UInt256.ofNat 2048) P = _
    rw [hP]
    rfl
  have hp : (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).productsBounded ((radix-1)^2) := ⟨productBound q4 n3 radix h_q4 h_n3, ⟨productBound q3 n4 radix h_q3 h_n4, ⟨⟨productBound x3 x4 radix h_x3 h_x4, productBound x3 x4 radix h_x3 h_x4⟩, True.intro⟩⟩⟩
  have hl : (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).literalsBounded C := by simp [sqE7, Expr.literalsBounded, hc]
  have hv := valueBound (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) ((radix-1)^2) C hp hl
  have hpc : (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).products ≤ 18 := by norm_num [sqE7, Expr.products]
  have hlc : (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).literals ≤ 1 := by norm_num [sqE7, Expr.literals]
  have hs : (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).value ≤ 18*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 18*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  have hCP : C ≤ residueModulus-1 := by
    norm_num [radix, residueModulus] at hC ⊢
    omega
  have hlP : (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt).literalsBounded (residueModulus-1) := by simp [sqE7, Expr.literalsBounded, le_trans hc hCP]
  have hr := CycleSubmission.DirectRecovery.expression_contract (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) (sqE7 c q3 q2 q1 q4 z0 z1 x2 x3 x4 n1 n2 n3 n4 P inv cnt) C
    (by norm_num [sqE7, Expr.count]) hlP rfl hC hs
  rw [hcar]
  refine ⟨hr, ?_⟩
  rw [hr]
  exact (CycleSubmission.Bounds.fullColumnBounds _ C hC hs).1

/-! ### sq column 8 (high) -/

def sqE8 (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) : Expr :=
  (Expr.add (Expr.product (q4) (n4)) (Expr.add (Expr.product (x4) (x4)) (Expr.literal (c))))

theorem sqE8_digit (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) :
    (sqCol8_o8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).toNat = (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).value % radix := by
  show (UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).low).toNat = _
  rw [Words.mask_literal]
  exact digitValue _

theorem sqE8_contract (c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt : UInt256) (C : Nat) (hP : P = CycleSubmission.WordArithmetic.P)
    (h_q4 : q4.toNat < radix) (h_n4 : n4.toNat < radix) (h_x4 : x4.toNat < radix) (hc : c.toNat ≤ C) (hC : C ≤ 18*(radix-1)) :
    (sqCol8_o0 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).toNat = (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).value / radix ∧ (sqCol8_o0 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).toNat ≤ 18*(radix-1) := by
  have hcar : (sqCol8_o0 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt) = CycleSubmission.DirectRecovery.carry ((sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).high CycleSubmission.WordArithmetic.P) (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).low := by
    show UInt256.mulMod (P + ((sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).high P - UInt256.land (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).low)) (UInt256.ofNat 2048) P = _
    rw [hP]
    rfl
  have hp : (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).productsBounded ((radix-1)^2) := ⟨productBound q4 n4 radix h_q4 h_n4, ⟨productBound x4 x4 radix h_x4 h_x4, True.intro⟩⟩
  have hl : (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).literalsBounded C := by simp [sqE8, Expr.literalsBounded, hc]
  have hv := valueBound (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt) ((radix-1)^2) C hp hl
  have hpc : (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).products ≤ 18 := by norm_num [sqE8, Expr.products]
  have hlc : (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).literals ≤ 1 := by norm_num [sqE8, Expr.literals]
  have hs : (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).value ≤ 18*(radix-1)^2+C := by
    calc _ ≤ _ := hv
      _ ≤ 18*((radix-1)^2)+1*C := Nat.add_le_add (Nat.mul_le_mul_right _ hpc) (Nat.mul_le_mul_right _ hlc)
      _ = _ := by rw [Nat.one_mul]
  have hCP : C ≤ residueModulus-1 := by
    norm_num [radix, residueModulus] at hC ⊢
    omega
  have hlP : (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt).literalsBounded (residueModulus-1) := by simp [sqE8, Expr.literalsBounded, le_trans hc hCP]
  have hr := CycleSubmission.DirectRecovery.expression_contract (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt) (sqE8 c q3 q2 q1 q4 z0 z1 z2 x3 x4 n1 n2 n3 n4 P inv cnt) C
    (by norm_num [sqE8, Expr.count]) hlP rfl hC hs
  rw [hcar]
  refine ⟨hr, ?_⟩
  rw [hr]
  exact (CycleSubmission.Bounds.fullColumnBounds _ C hC hs).1

end CycleSubmission.R5.SquareCols
