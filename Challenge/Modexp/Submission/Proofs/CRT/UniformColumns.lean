import Challenge.Modexp.Submission.Proofs.CRT.ColumnMemory
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000

namespace HistoricalSearch.UniformColumns
open EvmSemantics
open HistoricalSearch.CRTColumn HistoricalSearch.ColumnExpressions
open HistoricalSearch.GeneratedArithmetic HistoricalSearch.ConcreteArithmetic
open HistoricalSearch.ColumnContracts HistoricalSearch.ColumnMemory
open HistoricalSearch.MixedMontgomery

def sum (t : Nat) (carry minv : UInt256) (a n q : Nat → UInt256) : Nat :=
  match t with
  | 0 => col0Sum carry minv a n q
  | 1 => col1Sum carry minv a n q
  | 2 => col2Sum carry minv a n q
  | 3 => col3Sum carry minv a n q
  | 4 => col4Sum carry minv a n q
  | 5 => col5Sum carry minv a n q
  | 6 => col6Sum carry minv a n q
  | 7 => col7Sum carry minv a n q
  | 8 => col8Sum carry minv a n q
  | 9 => col9Sum carry minv a n q
  | 10 => col10Sum carry minv a n q
  | 11 => col11Sum carry minv a n q
  | 12 => col12Sum carry minv a n q
  | 13 => col13Sum carry minv a n q
  | 14 => col14Sum carry minv a n q
  | 15 => col15Sum carry minv a n q
  | _ => (a 8).toNat*(a 8).toNat+(q 8).toNat*(n 8).toNat+carry.toNat

def qs (t : Nat) (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 :=
  match t with
  | 0 => col0Qs carry minv a n q
  | 1 => col1Qs carry minv a n q
  | 2 => col2Qs carry minv a n q
  | 3 => col3Qs carry minv a n q
  | 4 => col4Qs carry minv a n q
  | 5 => col5Qs carry minv a n q
  | 6 => col6Qs carry minv a n q
  | 7 => col7Qs carry minv a n q
  | 8 => col8Qs carry minv a n q
  | _ => q

theorem carry (t : Nat) (ht : t < 16) (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < min t 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1))
    (N : Nat) (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0)
    : (words t carry minv a n q).carry.toNat = sum t carry minv a n q / radix := by
  interval_cases t
  · exact col0_actualCarry carry minv a n q ha hn hq hc (col0_cancels carry minv a n q N hn0 hinv)
  · exact col1_actualCarry carry minv a n q ha hn hq hc (col1_cancels carry minv a n q N hn0 hinv)
  · exact col2_actualCarry carry minv a n q ha hn hq hc (col2_cancels carry minv a n q N hn0 hinv)
  · exact col3_actualCarry carry minv a n q ha hn hq hc (col3_cancels carry minv a n q N hn0 hinv)
  · exact col4_actualCarry carry minv a n q ha hn hq hc (col4_cancels carry minv a n q N hn0 hinv)
  · exact col5_actualCarry carry minv a n q ha hn hq hc (col5_cancels carry minv a n q N hn0 hinv)
  · exact col6_actualCarry carry minv a n q ha hn hq hc (col6_cancels carry minv a n q N hn0 hinv)
  · exact col7_actualCarry carry minv a n q ha hn hq hc (col7_cancels carry minv a n q N hn0 hinv)
  · exact col8_actualCarry carry minv a n q ha hn hq hc
  · exact col9_actualCarry carry minv a n q ha hn hq hc
  · exact col10_actualCarry carry minv a n q ha hn hq hc
  · exact col11_actualCarry carry minv a n q ha hn hq hc
  · exact col12_actualCarry carry minv a n q ha hn hq hc
  · exact col13_actualCarry carry minv a n q ha hn hq hc
  · exact col14_actualCarry carry minv a n q ha hn hq hc
  · exact col15_actualCarry carry minv a n q ha hn hq hc

#print axioms carry

theorem carryBound (t : Nat) (ht : t < 16) (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < min t 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1))
    (N : Nat) (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0)
    : (words t carry minv a n q).carry.toNat ≤ 18*(radix-1) := by
  interval_cases t
  · exact col0_carryBound carry minv a n q ha hn hq hc N hn0 hinv
  · exact col1_carryBound carry minv a n q ha hn hq hc N hn0 hinv
  · exact col2_carryBound carry minv a n q ha hn hq hc N hn0 hinv
  · exact col3_carryBound carry minv a n q ha hn hq hc N hn0 hinv
  · exact col4_carryBound carry minv a n q ha hn hq hc N hn0 hinv
  · exact col5_carryBound carry minv a n q ha hn hq hc N hn0 hinv
  · exact col6_carryBound carry minv a n q ha hn hq hc N hn0 hinv
  · exact col7_carryBound carry minv a n q ha hn hq hc N hn0 hinv
  · exact col8_carryBound carry minv a n q ha hn hq hc
  · exact col9_carryBound carry minv a n q ha hn hq hc
  · exact col10_carryBound carry minv a n q ha hn hq hc
  · exact col11_carryBound carry minv a n q ha hn hq hc
  · exact col12_carryBound carry minv a n q ha hn hq hc
  · exact col13_carryBound carry minv a n q ha hn hq hc
  · exact col14_carryBound carry minv a n q ha hn hq hc
  · exact col15_carryBound carry minv a n q ha hn hq hc

#print axioms carryBound

theorem cancelRange (t : Nat) (ht : t < 9) (carry minv : UInt256) (a n q : Nat → UInt256) :
    (words t carry minv a n q).cancel.toNat < radix := by
  interval_cases t
  · exact col0_cancelRange carry minv a n q
  · exact col1_cancelRange carry minv a n q
  · exact col2_cancelRange carry minv a n q
  · exact col3_cancelRange carry minv a n q
  · exact col4_cancelRange carry minv a n q
  · exact col5_cancelRange carry minv a n q
  · exact col6_cancelRange carry minv a n q
  · exact col7_cancelRange carry minv a n q
  · exact (col8_cancelRange carry minv a n q).trans (by norm_num [radix])

theorem cancelTop (carry minv : UInt256) (a n q : Nat → UInt256) :
    (words 8 carry minv a n q).cancel.toNat < 2^96 := col8_cancelRange carry minv a n q

theorem digit (t : Nat) (ht : t < 16) (ht8 : 8 ≤ t) (carry minv : UInt256) (a n q : Nat → UInt256) :
    (words t carry minv a n q).digit.toNat = sum t carry minv a n q % radix := by
  interval_cases t
  · exact col8_digit carry minv a n q
  · exact col9_digit carry minv a n q
  · exact col10_digit carry minv a n q
  · exact col11_digit carry minv a n q
  · exact col12_digit carry minv a n q
  · exact col13_digit carry minv a n q
  · exact col14_digit carry minv a n q
  · exact col15_digit carry minv a n q

theorem cancelled (t : Nat) (ht : t < 8) (carry minv : UInt256) (a n q : Nat → UInt256) (N : Nat)
    (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    sum t carry minv a n q % radix = 0 := by
  interval_cases t
  · exact col0_cancels carry minv a n q N hn0 hinv
  · exact col1_cancels carry minv a n q N hn0 hinv
  · exact col2_cancels carry minv a n q N hn0 hinv
  · exact col3_cancels carry minv a n q N hn0 hinv
  · exact col4_cancels carry minv a n q N hn0 hinv
  · exact col5_cancels carry minv a n q N hn0 hinv
  · exact col6_cancels carry minv a n q N hn0 hinv
  · exact col7_cancels carry minv a n q N hn0 hinv

theorem cancelledTop (carry minv : UInt256) (a n q : Nat → UInt256) (N : Nat)
    (hn0 : (n 0).toNat = N % radix) (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    sum 8 carry minv a n q % 2^96 = 0 := col8_cancels carry minv a n q N hn0 hinv

theorem sumConvolution (t : Nat) (ht : t < 16) (carry minv : UInt256) (a n q : Nat → UInt256) :
    sum t carry minv a n q = (if t = 0 then 0 else carry.toNat) +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) t +
      convolution 9 (fun i => (qs t carry minv a n q i).toNat) (fun i => (n i).toNat) t := by
  interval_cases t
  · exact ConcreteConvolution.col0_high carry a n (col0Qs carry minv a n q)
  · exact ConcreteConvolution.col1_high carry a n (col1Qs carry minv a n q)
  · exact ConcreteConvolution.col2_high carry a n (col2Qs carry minv a n q)
  · exact ConcreteConvolution.col3_high carry a n (col3Qs carry minv a n q)
  · exact ConcreteConvolution.col4_high carry a n (col4Qs carry minv a n q)
  · exact ConcreteConvolution.col5_high carry a n (col5Qs carry minv a n q)
  · exact ConcreteConvolution.col6_high carry a n (col6Qs carry minv a n q)
  · exact ConcreteConvolution.col7_high carry a n (col7Qs carry minv a n q)
  · exact ConcreteConvolution.col8_high carry a n (col8Qs carry minv a n q)
  · exact ConcreteConvolution.col9_high carry a n (col9Qs carry minv a n q)
  · exact ConcreteConvolution.col10_high carry a n (col10Qs carry minv a n q)
  · exact ConcreteConvolution.col11_high carry a n (col11Qs carry minv a n q)
  · exact ConcreteConvolution.col12_high carry a n (col12Qs carry minv a n q)
  · exact ConcreteConvolution.col13_high carry a n (col13Qs carry minv a n q)
  · exact ConcreteConvolution.col14_high carry a n (col14Qs carry minv a n q)
  · exact ConcreteConvolution.col15_high carry a n (col15Qs carry minv a n q)

theorem qsPrefix (t : Nat) (ht : t < 9) (carry minv : UInt256) (a n q : Nat → UInt256) :
    qs t carry minv a n q = fun i => if i = t then (words t carry minv a n q).cancel
      else if i < t then q i else UInt256.ofNat 0 := by
  interval_cases t <;> rfl

theorem qsAfter (t : Nat) (ht : 9 ≤ t) (carry minv : UInt256) (a n q : Nat → UInt256) :
    qs t carry minv a n q = q := by
  cases t with
  | zero => omega
  | succ t =>
    rcases t with _|_|_|_|_|_|_|_|t <;> first | omega | rfl

#print axioms cancelRange
#print axioms digit
#print axioms cancelled
#print axioms sumConvolution
#print axioms qsPrefix
#print axioms qsAfter

end HistoricalSearch.UniformColumns
