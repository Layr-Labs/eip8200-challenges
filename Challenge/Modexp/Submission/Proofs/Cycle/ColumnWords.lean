import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square0
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square1
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square2
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square3
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square4
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square5
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square6
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square7
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square8
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square9
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square10
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square11
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square12
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square13
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square14
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square15
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Square16
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product0
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product1
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product2
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product3
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product4
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product5
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product6
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product7
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product8
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product9
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product10
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product11
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product12
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product13
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product14
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product15
import Challenge.Modexp.Submission.Proofs.Cycle.Columns.Product16

set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace CycleSubmission.ColumnWords
open EvmSemantics
open HistoricalSearch.ColumnExpressions HistoricalSearch.MixedMontgomery
open CycleSubmission.WordArithmetic CycleSubmission.Columns
inductive Kernel where | square | product
  deriving DecidableEq

def other (k : Kernel) (a b : Nat → UInt256) :=
  match k with | .square => a | .product => b

def high (k : Kernel) (i : Nat) (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr :=
  match k, i with
  | .square, 0 => square0High carry inv a b n q
  | .square, 1 => square1High carry inv a b n q
  | .square, 2 => square2High carry inv a b n q
  | .square, 3 => square3High carry inv a b n q
  | .square, 4 => square4High carry inv a b n q
  | .square, 5 => square5High carry inv a b n q
  | .square, 6 => square6High carry inv a b n q
  | .square, 7 => square7High carry inv a b n q
  | .square, 8 => square8High carry inv a b n q
  | .square, 9 => square9High carry inv a b n q
  | .square, 10 => square10High carry inv a b n q
  | .square, 11 => square11High carry inv a b n q
  | .square, 12 => square12High carry inv a b n q
  | .square, 13 => square13High carry inv a b n q
  | .square, 14 => square14High carry inv a b n q
  | .square, 15 => square15High carry inv a b n q
  | .square, 16 => square16High carry inv a b n q
  | .product, 0 => product0High carry inv a b n q
  | .product, 1 => product1High carry inv a b n q
  | .product, 2 => product2High carry inv a b n q
  | .product, 3 => product3High carry inv a b n q
  | .product, 4 => product4High carry inv a b n q
  | .product, 5 => product5High carry inv a b n q
  | .product, 6 => product6High carry inv a b n q
  | .product, 7 => product7High carry inv a b n q
  | .product, 8 => product8High carry inv a b n q
  | .product, 9 => product9High carry inv a b n q
  | .product, 10 => product10High carry inv a b n q
  | .product, 11 => product11High carry inv a b n q
  | .product, 12 => product12High carry inv a b n q
  | .product, 13 => product13High carry inv a b n q
  | .product, 14 => product14High carry inv a b n q
  | .product, 15 => product15High carry inv a b n q
  | .product, 16 => product16High carry inv a b n q
  | _, _ => Expr.literal (UInt256.ofNat 0)

def carryWord (k : Kernel) (i : Nat) (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 :=
  match k, i with
  | .square, 0 => square0Carry carry inv a b n q
  | .square, 1 => square1Carry carry inv a b n q
  | .square, 2 => square2Carry carry inv a b n q
  | .square, 3 => square3Carry carry inv a b n q
  | .square, 4 => square4Carry carry inv a b n q
  | .square, 5 => square5Carry carry inv a b n q
  | .square, 6 => square6Carry carry inv a b n q
  | .square, 7 => square7Carry carry inv a b n q
  | .square, 8 => square8Carry carry inv a b n q
  | .square, 9 => square9Carry carry inv a b n q
  | .square, 10 => square10Carry carry inv a b n q
  | .square, 11 => square11Carry carry inv a b n q
  | .square, 12 => square12Carry carry inv a b n q
  | .square, 13 => square13Carry carry inv a b n q
  | .square, 14 => square14Carry carry inv a b n q
  | .square, 15 => square15Carry carry inv a b n q
  | .square, 16 => square16Carry carry inv a b n q
  | .product, 0 => product0Carry carry inv a b n q
  | .product, 1 => product1Carry carry inv a b n q
  | .product, 2 => product2Carry carry inv a b n q
  | .product, 3 => product3Carry carry inv a b n q
  | .product, 4 => product4Carry carry inv a b n q
  | .product, 5 => product5Carry carry inv a b n q
  | .product, 6 => product6Carry carry inv a b n q
  | .product, 7 => product7Carry carry inv a b n q
  | .product, 8 => product8Carry carry inv a b n q
  | .product, 9 => product9Carry carry inv a b n q
  | .product, 10 => product10Carry carry inv a b n q
  | .product, 11 => product11Carry carry inv a b n q
  | .product, 12 => product12Carry carry inv a b n q
  | .product, 13 => product13Carry carry inv a b n q
  | .product, 14 => product14Carry carry inv a b n q
  | .product, 15 => product15Carry carry inv a b n q
  | .product, 16 => product16Carry carry inv a b n q
  | _, _ => UInt256.ofNat 0

def quotientWord (k : Kernel) (i : Nat) (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 :=
  match k, i with
  | .square, 0 => square0Q carry inv a b n q
  | .square, 1 => square1Q carry inv a b n q
  | .square, 2 => square2Q carry inv a b n q
  | .square, 3 => square3Q carry inv a b n q
  | .square, 4 => square4Q carry inv a b n q
  | .square, 5 => square5Q carry inv a b n q
  | .square, 6 => square6Q carry inv a b n q
  | .square, 7 => square7Q carry inv a b n q
  | .square, 8 => square8Q carry inv a b n q
  | .product, 0 => product0Q carry inv a b n q
  | .product, 1 => product1Q carry inv a b n q
  | .product, 2 => product2Q carry inv a b n q
  | .product, 3 => product3Q carry inv a b n q
  | .product, 4 => product4Q carry inv a b n q
  | .product, 5 => product5Q carry inv a b n q
  | .product, 6 => product6Q carry inv a b n q
  | .product, 7 => product7Q carry inv a b n q
  | .product, 8 => product8Q carry inv a b n q
  | _, _ => UInt256.ofNat 0

def digitWord (k : Kernel) (i : Nat) (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 :=
  match k, i with
  | .square, 9 => square9Digit carry inv a b n q
  | .square, 10 => square10Digit carry inv a b n q
  | .square, 11 => square11Digit carry inv a b n q
  | .square, 12 => square12Digit carry inv a b n q
  | .square, 13 => square13Digit carry inv a b n q
  | .square, 14 => square14Digit carry inv a b n q
  | .square, 15 => square15Digit carry inv a b n q
  | .square, 16 => square16Digit carry inv a b n q
  | .product, 9 => product9Digit carry inv a b n q
  | .product, 10 => product10Digit carry inv a b n q
  | .product, 11 => product11Digit carry inv a b n q
  | .product, 12 => product12Digit carry inv a b n q
  | .product, 13 => product13Digit carry inv a b n q
  | .product, 14 => product14Digit carry inv a b n q
  | .product, 15 => product15Digit carry inv a b n q
  | .product, 16 => product16Digit carry inv a b n q
  | _, _ => UInt256.ofNat 0

theorem quotient_bound (k : Kernel) (i : Nat) (hi : i < 9) (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (quotientWord k i carry inv a b n q).toNat < radix := by
  cases k <;> interval_cases i
  · exact square0_qbound carry inv a b n q
  · exact square1_qbound carry inv a b n q
  · exact square2_qbound carry inv a b n q
  · exact square3_qbound carry inv a b n q
  · exact square4_qbound carry inv a b n q
  · exact square5_qbound carry inv a b n q
  · exact square6_qbound carry inv a b n q
  · exact square7_qbound carry inv a b n q
  · exact square8_qbound carry inv a b n q
  · exact product0_qbound carry inv a b n q
  · exact product1_qbound carry inv a b n q
  · exact product2_qbound carry inv a b n q
  · exact product3_qbound carry inv a b n q
  · exact product4_qbound carry inv a b n q
  · exact product5_qbound carry inv a b n q
  · exact product6_qbound carry inv a b n q
  · exact product7_qbound carry inv a b n q
  · exact product8_qbound carry inv a b n q
theorem value_bound (k : Kernel) (i : Nat) (hi : i < 17) (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (high k i carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  cases k <;> interval_cases i
  · exact square0_bound carry inv a b n q ha hb hn hq hc
  · exact square1_bound carry inv a b n q ha hb hn hq hc
  · exact square2_bound carry inv a b n q ha hb hn hq hc
  · exact square3_bound carry inv a b n q ha hb hn hq hc
  · exact square4_bound carry inv a b n q ha hb hn hq hc
  · exact square5_bound carry inv a b n q ha hb hn hq hc
  · exact square6_bound carry inv a b n q ha hb hn hq hc
  · exact square7_bound carry inv a b n q ha hb hn hq hc
  · exact square8_bound carry inv a b n q ha hb hn hq hc
  · exact square9_bound carry inv a b n q ha hb hn hq hc
  · exact square10_bound carry inv a b n q ha hb hn hq hc
  · exact square11_bound carry inv a b n q ha hb hn hq hc
  · exact square12_bound carry inv a b n q ha hb hn hq hc
  · exact square13_bound carry inv a b n q ha hb hn hq hc
  · exact square14_bound carry inv a b n q ha hb hn hq hc
  · exact square15_bound carry inv a b n q ha hb hn hq hc
  · exact square16_bound carry inv a b n q ha hb hn hq hc
  · exact product0_bound carry inv a b n q ha hb hn hq hc
  · exact product1_bound carry inv a b n q ha hb hn hq hc
  · exact product2_bound carry inv a b n q ha hb hn hq hc
  · exact product3_bound carry inv a b n q ha hb hn hq hc
  · exact product4_bound carry inv a b n q ha hb hn hq hc
  · exact product5_bound carry inv a b n q ha hb hn hq hc
  · exact product6_bound carry inv a b n q ha hb hn hq hc
  · exact product7_bound carry inv a b n q ha hb hn hq hc
  · exact product8_bound carry inv a b n q ha hb hn hq hc
  · exact product9_bound carry inv a b n q ha hb hn hq hc
  · exact product10_bound carry inv a b n q ha hb hn hq hc
  · exact product11_bound carry inv a b n q ha hb hn hq hc
  · exact product12_bound carry inv a b n q ha hb hn hq hc
  · exact product13_bound carry inv a b n q ha hb hn hq hc
  · exact product14_bound carry inv a b n q ha hb hn hq hc
  · exact product15_bound carry inv a b n q ha hb hn hq hc
  · exact product16_bound carry inv a b n q ha hb hn hq hc
theorem contract (k : Kernel) (i : Nat) (hi : i < 17) (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1))
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hinv : (N*inv.toNat+1) % 2^256 = 0)
    (hnew : i < 9 → q i = quotientWord k i carry inv a b n q) :
    (carryWord k i carry inv a b n q).toNat = (high k i carry inv a b n q).value / radix ∧
    (if i < 9 then (high k i carry inv a b n q).value % radix = 0
     else (digitWord k i carry inv a b n q).toNat = (high k i carry inv a b n q).value % radix) := by
  cases k <;> interval_cases i
  · exact square0_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact square1_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact square2_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact square3_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact square4_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact square5_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact square6_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact square7_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact square8_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact ⟨square9_contract carry inv a b n q ha hb hn hq hc, square9_digit carry inv a b n q⟩
  · exact ⟨square10_contract carry inv a b n q ha hb hn hq hc, square10_digit carry inv a b n q⟩
  · exact ⟨square11_contract carry inv a b n q ha hb hn hq hc, square11_digit carry inv a b n q⟩
  · exact ⟨square12_contract carry inv a b n q ha hb hn hq hc, square12_digit carry inv a b n q⟩
  · exact ⟨square13_contract carry inv a b n q ha hb hn hq hc, square13_digit carry inv a b n q⟩
  · exact ⟨square14_contract carry inv a b n q ha hb hn hq hc, square14_digit carry inv a b n q⟩
  · exact ⟨square15_contract carry inv a b n q ha hb hn hq hc, square15_digit carry inv a b n q⟩
  · exact ⟨square16_contract carry inv a b n q ha hb hn hq hc, square16_digit carry inv a b n q⟩
  · exact product0_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact product1_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact product2_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact product3_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact product4_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact product5_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact product6_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact product7_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact product8_contract carry inv a b n q ha hb hn hq hc N hn0 hinv (hnew (by decide))
  · exact ⟨product9_contract carry inv a b n q ha hb hn hq hc, product9_digit carry inv a b n q⟩
  · exact ⟨product10_contract carry inv a b n q ha hb hn hq hc, product10_digit carry inv a b n q⟩
  · exact ⟨product11_contract carry inv a b n q ha hb hn hq hc, product11_digit carry inv a b n q⟩
  · exact ⟨product12_contract carry inv a b n q ha hb hn hq hc, product12_digit carry inv a b n q⟩
  · exact ⟨product13_contract carry inv a b n q ha hb hn hq hc, product13_digit carry inv a b n q⟩
  · exact ⟨product14_contract carry inv a b n q ha hb hn hq hc, product14_digit carry inv a b n q⟩
  · exact ⟨product15_contract carry inv a b n q ha hb hn hq hc, product15_digit carry inv a b n q⟩
  · exact ⟨product16_contract carry inv a b n q ha hb hn hq hc, product16_digit carry inv a b n q⟩
theorem value_convolution (k : Kernel) (i : Nat) (hi : i < 17) (carry inv : UInt256) (a b n q : Nat → UInt256)
    (hz : i = 0 → carry.toNat = 0) :
    (high k i carry inv a b n q).value = carry.toNat +
      convolution 9 (fun j => (a j).toNat) (fun j => (other k a b j).toNat) i +
      convolution 9 (fun j => (q j).toNat) (fun j => (n j).toNat) i := by
  cases k <;> interval_cases i
  · simpa only [high, other, hz rfl] using square0_convolution carry inv a b n q
  · exact square1_convolution carry inv a b n q
  · exact square2_convolution carry inv a b n q
  · exact square3_convolution carry inv a b n q
  · exact square4_convolution carry inv a b n q
  · exact square5_convolution carry inv a b n q
  · exact square6_convolution carry inv a b n q
  · exact square7_convolution carry inv a b n q
  · exact square8_convolution carry inv a b n q
  · exact square9_convolution carry inv a b n q
  · exact square10_convolution carry inv a b n q
  · exact square11_convolution carry inv a b n q
  · exact square12_convolution carry inv a b n q
  · exact square13_convolution carry inv a b n q
  · exact square14_convolution carry inv a b n q
  · exact square15_convolution carry inv a b n q
  · exact square16_convolution carry inv a b n q
  · simpa only [high, other, hz rfl] using product0_convolution carry inv a b n q
  · exact product1_convolution carry inv a b n q
  · exact product2_convolution carry inv a b n q
  · exact product3_convolution carry inv a b n q
  · exact product4_convolution carry inv a b n q
  · exact product5_convolution carry inv a b n q
  · exact product6_convolution carry inv a b n q
  · exact product7_convolution carry inv a b n q
  · exact product8_convolution carry inv a b n q
  · exact product9_convolution carry inv a b n q
  · exact product10_convolution carry inv a b n q
  · exact product11_convolution carry inv a b n q
  · exact product12_convolution carry inv a b n q
  · exact product13_convolution carry inv a b n q
  · exact product14_convolution carry inv a b n q
  · exact product15_convolution carry inv a b n q
  · exact product16_convolution carry inv a b n q
end CycleSubmission.ColumnWords
