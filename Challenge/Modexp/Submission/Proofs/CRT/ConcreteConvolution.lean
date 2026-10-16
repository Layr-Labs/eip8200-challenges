import Challenge.Modexp.Submission.Proofs.CRT.GeneratedArithmetic
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace HistoricalSearch.ConcreteConvolution
open EvmSemantics
open HistoricalSearch.ColumnExpressions HistoricalSearch.GeneratedArithmetic HistoricalSearch.MixedMontgomery

theorem col0_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col0High carry a n q).value = 0 +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 0 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 0 := by
  simp [col0High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col0_high

theorem col1_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col1High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 1 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 1 := by
  simp [col1High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col1_high

theorem col2_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col2High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 2 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 2 := by
  simp [col2High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col2_high

theorem col3_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col3High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 3 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 3 := by
  simp [col3High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col3_high

theorem col4_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col4High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 4 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 4 := by
  simp [col4High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col4_high

theorem col5_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col5High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 5 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 5 := by
  simp [col5High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col5_high

theorem col6_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col6High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 6 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 6 := by
  simp [col6High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col6_high

theorem col7_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col7High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 7 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 7 := by
  simp [col7High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col7_high

theorem col8_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col8High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 8 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 8 := by
  simp [col8High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col8_high

theorem col9_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col9High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 9 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 9 := by
  simp [col9High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col9_high

theorem col10_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col10High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 10 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 10 := by
  simp [col10High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col10_high

theorem col11_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col11High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 11 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 11 := by
  simp [col11High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col11_high

theorem col12_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col12High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 12 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 12 := by
  simp [col12High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col12_high

theorem col13_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col13High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 13 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 13 := by
  simp [col13High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col13_high

theorem col14_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col14High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 14 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 14 := by
  simp [col14High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col14_high

theorem col15_high (carry : UInt256) (a n q : Nat → UInt256) :
    (col15High carry a n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 15 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 15 := by
  simp [col15High, Expr.value, convolution, Finset.sum_filter, Finset.sum_product,
    Finset.sum_range_succ]
  ring

#print axioms col15_high

end HistoricalSearch.ConcreteConvolution
