import Challenge.Modexp.Submission.Proofs.R5.SquareCols
import Challenge.Modexp.Submission.Proofs.R5.SquareRun
import Challenge.Modexp.Submission.Proofs.R5.Kernel5
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

namespace CycleSubmission.R5.SquareMeaning
open EvmSemantics Challenge.EvmProof.Word
open HistoricalSearch.ColumnExpressions HistoricalSearch.WordCancellation HistoricalSearch.MixedMontgomery
open CycleSubmission.WordArithmetic
open CycleSubmission.R5.SquareCols CycleSubmission.R5.SquareRun

theorem K0_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < radix) (ha1 : a1.toNat < radix) (ha2 : a2.toNat < radix) (ha3 : a3.toNat < radix) (ha4 : a4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv ∧ (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat < radix ∧
    (post (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value % radix = 0 ∧
    (sqV0_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (post (sqE0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value / radix ∧ (sqV0_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  exact sqE0_contract a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N 0 hinv hP ha0 (by norm_num) hn0 hN

theorem K1_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < radix) (ha1 : a1.toNat < radix) (ha2 : a2.toNat < radix) (ha3 : a3.toNat < radix) (ha4 : a4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE1 (sqV0_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv ∧ (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat < radix ∧
    (post (sqE1 (sqV0_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value % radix = 0 ∧
    (sqV1_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (post (sqE1 (sqV0_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value / radix ∧ (sqV1_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  exact sqE1_contract (sqV0_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N (18*(radix-1)) hinv hP (K0).2.1 hn1 ha0 ha1 (K0).2.2.2.2 le_rfl hn0 hN

theorem K2_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < radix) (ha1 : a1.toNat < radix) (ha2 : a2.toNat < radix) (ha3 : a3.toNat < radix) (ha4 : a4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE2 (sqV1_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv ∧ (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat < radix ∧
    (post (sqE2 (sqV1_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value % radix = 0 ∧
    (sqV2_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (post (sqE2 (sqV1_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value / radix ∧ (sqV2_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K1 := K1_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  exact sqE2_contract (sqV1_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N (18*(radix-1)) hinv hP (K1).2.1 hn1 (K0).2.1 hn2 ha1 ha0 ha2 (K1).2.2.2.2 le_rfl hn0 hN

theorem K3_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < radix) (ha1 : a1.toNat < radix) (ha2 : a2.toNat < radix) (ha3 : a3.toNat < radix) (ha4 : a4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE3 (sqV2_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv ∧ (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat < radix ∧
    (post (sqE3 (sqV2_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value % radix = 0 ∧
    (sqV3_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (post (sqE3 (sqV2_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value / radix ∧ (sqV3_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K1 := K1_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K2 := K2_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  exact sqE3_contract (sqV2_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N (18*(radix-1)) hinv hP (K2).2.1 hn1 (K1).2.1 hn2 (K0).2.1 hn3 ha1 ha2 ha0 ha3 (K2).2.2.2.2 le_rfl hn0 hN

theorem K4_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < radix) (ha1 : a1.toNat < radix) (ha2 : a2.toNat < radix) (ha3 : a3.toNat < radix) (ha4 : a4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) = quotient (sqE4 (sqV3_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv ∧ (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat < radix ∧
    (post (sqE4 (sqV3_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value % radix = 0 ∧
    (sqV4_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (post (sqE4 (sqV3_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) ninv n0).value / radix ∧ (sqV4_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K1 := K1_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K2 := K2_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K3 := K3_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  exact sqE4_contract (sqV3_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N (18*(radix-1)) hinv hP (K3).2.1 hn1 (K2).2.1 hn2 (K1).2.1 hn3 (K0).2.1 hn4 ha2 ha1 ha3 ha0 ha4 (K3).2.2.2.2 le_rfl hn0 hN

theorem K5_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < radix) (ha1 : a1.toNat < radix) (ha2 : a2.toNat < radix) (ha3 : a3.toNat < radix) (ha4 : a4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqV5_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (sqE5 (sqV4_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt).value / radix ∧ (sqV5_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K1 := K1_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K2 := K2_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K3 := K3_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K4 := K4_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  exact sqE5_contract (sqV4_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt (18*(radix-1)) hP (K4).2.1 hn1 (K3).2.1 hn2 (K2).2.1 hn3 (K1).2.1 hn4 ha2 ha3 ha1 ha4 (K4).2.2.2.2 le_rfl

theorem Z5_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) :
    (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (sqE5 (sqV4_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt).value % radix :=
  sqE5_digit (sqV4_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt

theorem K6_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < radix) (ha1 : a1.toNat < radix) (ha2 : a2.toNat < radix) (ha3 : a3.toNat < radix) (ha4 : a4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqV6_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (sqE6 (sqV5_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt).value / radix ∧ (sqV6_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K1 := K1_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K2 := K2_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K3 := K3_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K4 := K4_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K5 := K5_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  exact sqE6_contract (sqV5_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt (18*(radix-1)) hP (K4).2.1 hn2 (K3).2.1 hn3 (K2).2.1 hn4 ha3 ha2 ha4 (K5).2 le_rfl

theorem Z6_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) :
    (sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (sqE6 (sqV5_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt).value % radix :=
  sqE6_digit (sqV5_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt

theorem K7_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < radix) (ha1 : a1.toNat < radix) (ha2 : a2.toNat < radix) (ha3 : a3.toNat < radix) (ha4 : a4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqV7_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (sqE7 (sqV6_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a2 a3 a4 n1 n2 n3 n4 P inv cnt).value / radix ∧ (sqV7_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K1 := K1_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K2 := K2_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K3 := K3_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K4 := K4_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K5 := K5_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K6 := K6_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  exact sqE7_contract (sqV6_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a2 a3 a4 n1 n2 n3 n4 P inv cnt (18*(radix-1)) hP (K4).2.1 hn3 (K3).2.1 hn4 ha3 ha4 (K6).2 le_rfl

theorem Z7_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) :
    (sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (sqE7 (sqV6_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a2 a3 a4 n1 n2 n3 n4 P inv cnt).value % radix :=
  sqE7_digit (sqV6_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a2 a3 a4 n1 n2 n3 n4 P inv cnt

theorem K8_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < radix) (ha1 : a1.toNat < radix) (ha2 : a2.toNat < radix) (ha3 : a3.toNat < radix) (ha4 : a4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (sqV8_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (sqE8 (sqV7_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a3 a4 n1 n2 n3 n4 P inv cnt).value / radix ∧ (sqV8_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat ≤ 18*(radix-1) := by
  have K0 := K0_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K1 := K1_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K2 := K2_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K3 := K3_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K4 := K4_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K5 := K5_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K6 := K6_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K7 := K7_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  exact sqE8_contract (sqV7_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a3 a4 n1 n2 n3 n4 P inv cnt (18*(radix-1)) hP (K4).2.1 hn4 ha4 (K7).2 le_rfl

theorem Z8_stmt (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) :
    (sqV8_8 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat = (sqE8 (sqV7_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a3 a4 n1 n2 n3 n4 P inv cnt).value % radix :=
  sqE8_digit (sqV7_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) a3 a4 n1 n2 n3 n4 P inv cnt

def sqCd (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : Nat → Nat
  | 0 => 0
  | 1 => (sqV0_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 2 => (sqV1_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 3 => (sqV2_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 4 => (sqV3_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 5 => (sqV4_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 6 => (sqV5_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 7 => (sqV6_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 8 => (sqV7_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 9 => (sqV8_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | _ => 0

def sqDd (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : Nat → Nat
  | 5 => (sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 6 => (sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 7 => (sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 8 => (sqV8_8 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 9 => (sqV8_0 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | _ => 0

def sqQd (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : Nat → Nat
  | 0 => (sqV0_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 1 => (sqV1_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 2 => (sqV2_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 3 => (sqV3_1 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | 4 => (sqV4_4 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0).toNat
  | _ => 0

def sqXd (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : Nat → Nat
  | 0 => a0.toNat
  | 1 => a1.toNat
  | 2 => a2.toNat
  | 3 => a3.toNat
  | 4 => a4.toNat
  | _ => 0

def sqYd (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : Nat → Nat
  | 0 => a0.toNat
  | 1 => a1.toNat
  | 2 => a2.toNat
  | 3 => a3.toNat
  | 4 => a4.toNat
  | _ => 0

def sqNd (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) : Nat → Nat
  | 0 => n0.toNat
  | 1 => n1.toNat
  | 2 => n2.toNat
  | 3 => n3.toNat
  | 4 => n4.toNat
  | _ => 0

theorem sq_exact (a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 : UInt256) (ninv : UInt256) (N : Nat)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (ha0 : a0.toNat < radix) (ha1 : a1.toNat < radix) (ha2 : a2.toNat < radix) (ha3 : a3.toNat < radix) (ha4 : a4.toNat < radix)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0) :
    (∀ i < 5, (sqQd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 i) < radix) ∧ (∀ i < 4, (sqDd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 (5+i)) < radix) ∧
    weighted radix 5 (fun i => sqDd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 (5+i)) * radix^5 =
      weighted radix 5 (sqXd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) * weighted radix 5 (sqYd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) +
      weighted radix 5 (sqQd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) * weighted radix 5 (sqNd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) := by
  have K0 := K0_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K1 := K1_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K2 := K2_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K3 := K3_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K4 := K4_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K5 := K5_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K6 := K6_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K7 := K7_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
  have K8 := K8_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0 ninv N hinv hP ha0 ha1 ha2 ha3 ha4 hn1 hn2 hn3 hn4 hn0 hN
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
    · show ((sqV5_5 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)).toNat < radix
      rw [Z5_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · show ((sqV6_6 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)).toNat < radix
      rw [Z6_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · show ((sqV7_7 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)).toNat < radix
      rw [Z7_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · show ((sqV8_8 a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0)).toNat < radix
      rw [Z8_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  apply Kernel5.exact5 radix (sqXd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqYd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqQd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqNd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqDd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) (sqCd a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0) rfl rfl
  · intro i hi; interval_cases i <;> rfl
  · intro i hi
    interval_cases i
    · -- column 0
      simp only [sqDd, sqCd, sqXd, sqYd, sqQd, sqNd, Kernel5.column0, Nat.zero_add]
      rw [(K0).2.2.2.1, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (K0).2.2.1)]
      rw [(K0).1]
      simp only [post, sqE0, Expr.value]
      ring
    · -- column 1
      simp only [sqDd, sqCd, sqXd, sqYd, sqQd, sqNd, Kernel5.column1, Nat.zero_add]
      rw [(K1).2.2.2.1, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (K1).2.2.1)]
      rw [(K1).1]
      simp only [post, sqE1, Expr.value]
      ring
    · -- column 2
      simp only [sqDd, sqCd, sqXd, sqYd, sqQd, sqNd, Kernel5.column2, Nat.zero_add]
      rw [(K2).2.2.2.1, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (K2).2.2.1)]
      rw [(K2).1]
      simp only [post, sqE2, Expr.value]
      ring
    · -- column 3
      simp only [sqDd, sqCd, sqXd, sqYd, sqQd, sqNd, Kernel5.column3, Nat.zero_add]
      rw [(K3).2.2.2.1, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (K3).2.2.1)]
      rw [(K3).1]
      simp only [post, sqE3, Expr.value]
      ring
    · -- column 4
      simp only [sqDd, sqCd, sqXd, sqYd, sqQd, sqNd, Kernel5.column4, Nat.zero_add]
      rw [(K4).2.2.2.1, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (K4).2.2.1)]
      rw [(K4).1]
      simp only [post, sqE4, Expr.value]
      ring
    · -- column 5
      simp only [sqDd, sqCd, sqXd, sqYd, sqQd, sqNd, Kernel5.column5]
      rw [(Z5_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0), (K5).1, Nat.mod_add_div]
      simp only [sqE5, Expr.value]
      ring
    · -- column 6
      simp only [sqDd, sqCd, sqXd, sqYd, sqQd, sqNd, Kernel5.column6]
      rw [(Z6_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0), (K6).1, Nat.mod_add_div]
      simp only [sqE6, Expr.value]
      ring
    · -- column 7
      simp only [sqDd, sqCd, sqXd, sqYd, sqQd, sqNd, Kernel5.column7]
      rw [(Z7_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0), (K7).1, Nat.mod_add_div]
      simp only [sqE7, Expr.value]
      ring
    · -- column 8
      simp only [sqDd, sqCd, sqXd, sqYd, sqQd, sqNd, Kernel5.column8]
      rw [(Z8_stmt a0 a1 a2 a3 a4 n1 n2 n3 n4 P inv cnt n0), (K8).1, Nat.mod_add_div]
      simp only [sqE8, Expr.value]
      ring
    · -- column 9: no terms
      simp only [sqDd, sqCd, Kernel5.column9]
      ring

end CycleSubmission.R5.SquareMeaning
