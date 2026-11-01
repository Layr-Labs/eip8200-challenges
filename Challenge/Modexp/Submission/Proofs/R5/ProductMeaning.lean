import Challenge.Modexp.Submission.Proofs.R5.ProductCols
import Challenge.Modexp.Submission.Proofs.R5.ProductRun
import Challenge.Modexp.Submission.Proofs.R5.Kernel5
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

namespace CycleSubmission.R5.ProductMeaning
open EvmSemantics Challenge.EvmProof.Word
open HistoricalSearch.ColumnExpressions HistoricalSearch.WordCancellation HistoricalSearch.MixedMontgomery
open CycleSubmission.WordArithmetic
open CycleSubmission.R5.ProductCols CycleSubmission.R5.ProductRun

theorem K0_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (hx0 : x0.toNat < radix) (hx1 : x1.toNat < radix) (hx2 : x2.toNat < radix) (hx3 : x3.toNat < radix) (hx4 : x4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hb0 : b0.toNat < radix) (hb1 : b1.toNat < radix) (hb2 : b2.toNat < radix) (hb3 : b3.toNat < radix) (hb4 : b4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) = quotient (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) ninv ∧ (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat < radix ∧
    (post (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) ninv n0).value % radix = 0 ∧
    (prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (post (prE0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0) ninv n0).value / radix ∧ (prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat ≤ 18*(radix-1) := by
  exact prE0_contract x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 n0 ninv N 0 hinv hP hx0 hb0 (by norm_num) hn0 hN

theorem K1_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (hx0 : x0.toNat < radix) (hx1 : x1.toNat < radix) (hx2 : x2.toNat < radix) (hx3 : x3.toNat < radix) (hx4 : x4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hb0 : b0.toNat < radix) (hb1 : b1.toNat < radix) (hb2 : b2.toNat < radix) (hb3 : b3.toNat < radix) (hb4 : b4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) = quotient (prE1 (prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) ninv ∧ (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat < radix ∧
    (post (prE1 (prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) ninv n0).value % radix = 0 ∧
    (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (post (prE1 (prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0) ninv n0).value / radix ∧ (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  exact prE1_contract (prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 n0 ninv N (18*(radix-1)) hinv hP (K0).2.1 hn1 hx1 hb0 hx0 hb1 (K0).2.2.2.2 le_rfl hn0 hN

theorem K2_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (hx0 : x0.toNat < radix) (hx1 : x1.toNat < radix) (hx2 : x2.toNat < radix) (hx3 : x3.toNat < radix) (hx4 : x4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hb0 : b0.toNat < radix) (hb1 : b1.toNat < radix) (hb2 : b2.toNat < radix) (hb3 : b3.toNat < radix) (hb4 : b4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) = quotient (prE2 (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) ninv ∧ (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat < radix ∧
    (post (prE2 (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) ninv n0).value % radix = 0 ∧
    (prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (post (prE2 (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0) ninv n0).value / radix ∧ (prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K1 := K1_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  exact prE2_contract (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 n0 ninv N (18*(radix-1)) hinv hP (K1).2.1 hn1 (K0).2.1 hn2 hx2 hb0 hx1 hb1 hx0 hb2 (K1).2.2.2.2 le_rfl hn0 hN

theorem K3_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (hx0 : x0.toNat < radix) (hx1 : x1.toNat < radix) (hx2 : x2.toNat < radix) (hx3 : x3.toNat < radix) (hx4 : x4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hb0 : b0.toNat < radix) (hb1 : b1.toNat < radix) (hb2 : b2.toNat < radix) (hb3 : b3.toNat < radix) (hb4 : b4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) = quotient (prE3 (prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) ninv ∧ (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat < radix ∧
    (post (prE3 (prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) ninv n0).value % radix = 0 ∧
    (prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (post (prE3 (prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0) ninv n0).value / radix ∧ (prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K1 := K1_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K2 := K2_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  exact prE3_contract (prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 n0 ninv N (18*(radix-1)) hinv hP (K2).2.1 hn1 (K1).2.1 hn2 (K0).2.1 hn3 hx3 hb0 hx2 hb1 hx1 hb2 hx0 hb3 (K2).2.2.2.2 le_rfl hn0 hN

theorem K4_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (hx0 : x0.toNat < radix) (hx1 : x1.toNat < radix) (hx2 : x2.toNat < radix) (hx3 : x3.toNat < radix) (hx4 : x4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hb0 : b0.toNat < radix) (hb1 : b1.toNat < radix) (hb2 : b2.toNat < radix) (hb3 : b3.toNat < radix) (hb4 : b4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) = quotient (prE4 (prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) ninv ∧ (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat < radix ∧
    (post (prE4 (prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) ninv n0).value % radix = 0 ∧
    (prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (post (prE4 (prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0) ninv n0).value / radix ∧ (prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K1 := K1_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K2 := K2_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K3 := K3_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  exact prE4_contract (prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 ninv N (18*(radix-1)) hinv hP (K3).2.1 hn1 (K2).2.1 hn2 (K1).2.1 hn3 (K0).2.1 hn4 hx4 hb0 hx3 hb1 hx2 hb2 hx1 hb3 hx0 hb4 (K3).2.2.2.2 le_rfl hn0 hN

theorem K5_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (hx0 : x0.toNat < radix) (hx1 : x1.toNat < radix) (hx2 : x2.toNat < radix) (hx3 : x3.toNat < radix) (hx4 : x4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hb0 : b0.toNat < radix) (hb1 : b1.toNat < radix) (hb2 : b2.toNat < radix) (hb3 : b3.toNat < radix) (hb4 : b4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV5_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (prE5 (prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).value / radix ∧ (prV5_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K1 := K1_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K2 := K2_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K3 := K3_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K4 := K4_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  exact prE5_contract (prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M (18*(radix-1)) hP (K4).2.1 hn1 (K3).2.1 hn2 (K2).2.1 hn3 (K1).2.1 hn4 hx4 hb1 hx3 hb2 hx2 hb3 hx1 hb4 (K4).2.2.2.2 le_rfl hM

theorem Z5_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (prE5 (prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M).value % radix :=
  prE5_digit (prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b1 b2 b3 b4 M hM

theorem K6_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (hx0 : x0.toNat < radix) (hx1 : x1.toNat < radix) (hx2 : x2.toNat < radix) (hx3 : x3.toNat < radix) (hx4 : x4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hb0 : b0.toNat < radix) (hb1 : b1.toNat < radix) (hb2 : b2.toNat < radix) (hb3 : b3.toNat < radix) (hb4 : b4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV6_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (prE6 (prV5_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).value / radix ∧ (prV6_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K1 := K1_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K2 := K2_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K3 := K3_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K4 := K4_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K5 := K5_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  exact prE6_contract (prV5_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M (18*(radix-1)) hP (K4).2.1 hn2 (K3).2.1 hn3 (K2).2.1 hn4 hx4 hb2 hx3 hb3 hx2 hb4 (K5).2 le_rfl hM

theorem Z6_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (prE6 (prV5_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M).value % radix :=
  prE6_digit (prV5_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b2 b3 b4 M hM

theorem K7_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (hx0 : x0.toNat < radix) (hx1 : x1.toNat < radix) (hx2 : x2.toNat < radix) (hx3 : x3.toNat < radix) (hx4 : x4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hb0 : b0.toNat < radix) (hb1 : b1.toNat < radix) (hb2 : b2.toNat < radix) (hb3 : b3.toNat < radix) (hb4 : b4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV7_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (prE7 (prV6_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).value / radix ∧ (prV7_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K1 := K1_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K2 := K2_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K3 := K3_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K4 := K4_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K5 := K5_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K6 := K6_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  exact prE7_contract (prV6_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M (18*(radix-1)) hP (K4).2.1 hn3 (K3).2.1 hn4 hx4 hb3 hx3 hb4 (K6).2 le_rfl hM

theorem Z7_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV7_7 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (prE7 (prV6_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M).value % radix :=
  prE7_digit (prV6_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x2 x3 x4 n1 n2 n3 n4 P inv cntp b3 b4 M hM

theorem K8_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (hx0 : x0.toNat < radix) (hx1 : x1.toNat < radix) (hx2 : x2.toNat < radix) (hx3 : x3.toNat < radix) (hx4 : x4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hb0 : b0.toNat < radix) (hb1 : b1.toNat < radix) (hb2 : b2.toNat < radix) (hb3 : b3.toNat < radix) (hb4 : b4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV8_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (prE8 (prV7_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV7_7 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x3 x4 n1 n2 n3 n4 P inv cntp b4 M).value / radix ∧ (prV8_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K1 := K1_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K2 := K2_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K3 := K3_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K4 := K4_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K5 := K5_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K6 := K6_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K7 := K7_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  exact prE8_contract (prV7_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV7_7 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x3 x4 n1 n2 n3 n4 P inv cntp b4 M (18*(radix-1)) hP (K4).2.1 hn4 hx4 hb4 (K7).2 le_rfl hM

theorem Z8_stmt (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (prV8_8 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat = (prE8 (prV7_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV7_7 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x3 x4 n1 n2 n3 n4 P inv cntp b4 M).value % radix :=
  prE8_digit (prV7_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prV7_7 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) x3 x4 n1 n2 n3 n4 P inv cntp b4 M hM

def prCd (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : Nat → Nat
  | 0 => 0
  | 1 => (prV0_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 2 => (prV1_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 3 => (prV2_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 4 => (prV3_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 5 => (prV4_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 6 => (prV5_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 7 => (prV6_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 8 => (prV7_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 9 => (prV8_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | _ => 0

def prDd (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : Nat → Nat
  | 5 => (prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 6 => (prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 7 => (prV7_7 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 8 => (prV8_8 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 9 => (prV8_0 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | _ => 0

def prQd (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : Nat → Nat
  | 0 => (prV0_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 1 => (prV1_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 2 => (prV2_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 3 => (prV3_1 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | 4 => (prV4_4 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M).toNat
  | _ => 0

def prXd (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : Nat → Nat
  | 0 => x0.toNat
  | 1 => x1.toNat
  | 2 => x2.toNat
  | 3 => x3.toNat
  | 4 => x4.toNat
  | _ => 0

def prYd (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : Nat → Nat
  | 0 => b0.toNat
  | 1 => b1.toNat
  | 2 => b2.toNat
  | 3 => b3.toNat
  | 4 => b4.toNat
  | _ => 0

def prNd (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : Nat → Nat
  | 0 => n0.toNat
  | 1 => n1.toNat
  | 2 => n2.toNat
  | 3 => n3.toNat
  | 4 => n4.toNat
  | _ => 0

theorem pr_exact (x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (hx0 : x0.toNat < radix) (hx1 : x1.toNat < radix) (hx2 : x2.toNat < radix) (hx3 : x3.toNat < radix) (hx4 : x4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hb0 : b0.toNat < radix) (hb1 : b1.toNat < radix) (hb2 : b2.toNat < radix) (hb3 : b3.toNat < radix) (hb4 : b4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) (hM : M = UInt256.ofNat (2^240 - 1)) :
    (∀ i < 5, (prQd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M i) < radix) ∧ (∀ i < 4, (prDd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M (5+i)) < radix) ∧
    weighted radix 5 (fun i => prDd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M (5+i)) * radix^5 =
      weighted radix 5 (prXd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) * weighted radix 5 (prYd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) +
      weighted radix 5 (prQd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) * weighted radix 5 (prNd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) := by
  have K0 := K0_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K1 := K1_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K2 := K2_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K3 := K3_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K4 := K4_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K5 := K5_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K6 := K6_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K7 := K7_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  have K8 := K8_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN hM
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · exact (K0).2.1
    · exact (K1).2.1
    · exact (K2).2.1
    · exact (K3).2.1
    · exact (K4).2.1
  · intro i hi
    interval_cases i
    · show ((prV5_5 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)).toNat < radix
      rw [Z5_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M hM]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · show ((prV6_6 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)).toNat < radix
      rw [Z6_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M hM]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · show ((prV7_7 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)).toNat < radix
      rw [Z7_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M hM]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · show ((prV8_8 x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M)).toNat < radix
      rw [Z8_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M hM]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  apply Kernel5.exact5 radix (prXd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prYd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prQd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prNd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prDd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) (prCd x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M) rfl rfl
  · intro i hi; interval_cases i <;> rfl
  · intro i hi
    interval_cases i
    · -- column 0
      simp only [prDd, prCd, prXd, prYd, prQd, prNd, Kernel5.column0, Nat.zero_add]
      rw [(K0).2.2.2.1, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (K0).2.2.1)]
      rw [(K0).1]
      simp only [post, prE0, Expr.value]
      ring
    · -- column 1
      simp only [prDd, prCd, prXd, prYd, prQd, prNd, Kernel5.column1, Nat.zero_add]
      rw [(K1).2.2.2.1, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (K1).2.2.1)]
      rw [(K1).1]
      simp only [post, prE1, Expr.value]
      ring
    · -- column 2
      simp only [prDd, prCd, prXd, prYd, prQd, prNd, Kernel5.column2, Nat.zero_add]
      rw [(K2).2.2.2.1, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (K2).2.2.1)]
      rw [(K2).1]
      simp only [post, prE2, Expr.value]
      ring
    · -- column 3
      simp only [prDd, prCd, prXd, prYd, prQd, prNd, Kernel5.column3, Nat.zero_add]
      rw [(K3).2.2.2.1, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (K3).2.2.1)]
      rw [(K3).1]
      simp only [post, prE3, Expr.value]
      ring
    · -- column 4
      simp only [prDd, prCd, prXd, prYd, prQd, prNd, Kernel5.column4, Nat.zero_add]
      rw [(K4).2.2.2.1, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (K4).2.2.1)]
      rw [(K4).1]
      simp only [post, prE4, Expr.value]
      ring
    · -- column 5
      simp only [prDd, prCd, prXd, prYd, prQd, prNd, Kernel5.column5]
      rw [(Z5_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M hM), (K5).1, Nat.mod_add_div]
      simp only [prE5, Expr.value]
      ring
    · -- column 6
      simp only [prDd, prCd, prXd, prYd, prQd, prNd, Kernel5.column6]
      rw [(Z6_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M hM), (K6).1, Nat.mod_add_div]
      simp only [prE6, Expr.value]
      ring
    · -- column 7
      simp only [prDd, prCd, prXd, prYd, prQd, prNd, Kernel5.column7]
      rw [(Z7_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M hM), (K7).1, Nat.mod_add_div]
      simp only [prE7, Expr.value]
      ring
    · -- column 8
      simp only [prDd, prCd, prXd, prYd, prQd, prNd, Kernel5.column8]
      rw [(Z8_stmt x0 x1 x2 x3 x4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M hM), (K8).1, Nat.mod_add_div]
      simp only [prE8, Expr.value]
      ring
    · -- column 9: no terms
      simp only [prDd, prCd, Kernel5.column9]
      ring

end CycleSubmission.R5.ProductMeaning
