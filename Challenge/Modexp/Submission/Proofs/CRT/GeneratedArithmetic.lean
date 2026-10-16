import Challenge.Modexp.Submission.Proofs.CRT.ColumnExpressions
import Challenge.Modexp.Submission.Proofs.CRT.MixedMontgomery
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace HistoricalSearch.GeneratedArithmetic
open EvmSemantics
open HistoricalSearch.CRTColumn HistoricalSearch.GenericColumn
open HistoricalSearch.ColumnExpressions HistoricalSearch.MixedMontgomery
open HistoricalSearch.CRTExecution

def radix : Nat := 2^244
def modulusWord : UInt256 := UInt256.ofNat residueModulus

def col0High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 0)) (Expr.product (a 0) (a 0)))
def col0Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 0)) (Expr.product (a 0) (a 0)))

theorem col0_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col0High carry a n q).value = (col0Low carry a n q).value := by
  rfl

theorem col0_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col0High carry a n q).high modulusWord) (col0Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col0High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col0High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 0) radix (hn 0 (by decide)) (hq 0 (by decide)), productBound (a 0) (a 0) radix (ha 0 (by decide)) (ha 0 (by decide))⟩
  have hlit : (col0High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, True.intro⟩
  have hlitC : (col0High carry a n q).literalsBounded carry.toNat := by
    simp [col0High, Expr.literalsBounded]
  have hbound := valueBound (col0High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col0High carry a n q).products ≤ 18 := by norm_num [col0High, Expr.products]
  have hl : (col0High carry a n q).literals ≤ 1 := by norm_num [col0High, Expr.literals]
  have hcount : (col0High carry a n q).count ≤ 19 := by norm_num [col0High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col0High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col0High carry a n q) (col0Low carry a n q) carry.toNat hcount hlit
    (col0_sameValue carry a n q) hc hsum

#print axioms col0_carry

def col1High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 1)) (Expr.add (Expr.product (n 1) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 1) (a 0)) (Expr.product (a 1) (a 0))))))
def col1Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 1)) (Expr.add (Expr.product (n 1) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 1) (a 0)) (Expr.product (a 1) (a 0))))))

theorem col1_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col1High carry a n q).value = (col1Low carry a n q).value := by
  rfl

theorem col1_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col1High carry a n q).high modulusWord) (col1Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col1High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col1High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 1) radix (hn 0 (by decide)) (hq 1 (by decide)), ⟨productBound (n 1) (q 0) radix (hn 1 (by decide)) (hq 0 (by decide)), ⟨True.intro, ⟨productBound (a 1) (a 0) radix (ha 1 (by decide)) (ha 0 (by decide)), productBound (a 1) (a 0) radix (ha 1 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩
  have hlit : (col1High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨True.intro, True.intro⟩⟩⟩⟩
  have hlitC : (col1High carry a n q).literalsBounded carry.toNat := by
    simp [col1High, Expr.literalsBounded]
  have hbound := valueBound (col1High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col1High carry a n q).products ≤ 18 := by norm_num [col1High, Expr.products]
  have hl : (col1High carry a n q).literals ≤ 1 := by norm_num [col1High, Expr.literals]
  have hcount : (col1High carry a n q).count ≤ 19 := by norm_num [col1High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col1High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col1High carry a n q) (col1Low carry a n q) carry.toNat hcount hlit
    (col1_sameValue carry a n q) hc hsum

#print axioms col1_carry

def col2High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 2)) (Expr.add (Expr.product (n 1) (q 1)) (Expr.add (Expr.product (n 2) (q 0)) (Expr.add (Expr.product (a 1) (a 1)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 2) (a 0)) (Expr.product (a 2) (a 0))))))))
def col2Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 2)) (Expr.add (Expr.product (n 1) (q 1)) (Expr.add (Expr.product (n 2) (q 0)) (Expr.add (Expr.product (a 1) (a 1)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 2) (a 0)) (Expr.product (a 2) (a 0))))))))

theorem col2_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col2High carry a n q).value = (col2Low carry a n q).value := by
  rfl

theorem col2_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col2High carry a n q).high modulusWord) (col2Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col2High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col2High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 2) radix (hn 0 (by decide)) (hq 2 (by decide)), ⟨productBound (n 1) (q 1) radix (hn 1 (by decide)) (hq 1 (by decide)), ⟨productBound (n 2) (q 0) radix (hn 2 (by decide)) (hq 0 (by decide)), ⟨productBound (a 1) (a 1) radix (ha 1 (by decide)) (ha 1 (by decide)), ⟨True.intro, ⟨productBound (a 2) (a 0) radix (ha 2 (by decide)) (ha 0 (by decide)), productBound (a 2) (a 0) radix (ha 2 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩
  have hlit : (col2High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩
  have hlitC : (col2High carry a n q).literalsBounded carry.toNat := by
    simp [col2High, Expr.literalsBounded]
  have hbound := valueBound (col2High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col2High carry a n q).products ≤ 18 := by norm_num [col2High, Expr.products]
  have hl : (col2High carry a n q).literals ≤ 1 := by norm_num [col2High, Expr.literals]
  have hcount : (col2High carry a n q).count ≤ 19 := by norm_num [col2High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col2High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col2High carry a n q) (col2Low carry a n q) carry.toNat hcount hlit
    (col2_sameValue carry a n q) hc hsum

#print axioms col2_carry

def col3High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 3)) (Expr.add (Expr.product (n 1) (q 2)) (Expr.add (Expr.product (n 2) (q 1)) (Expr.add (Expr.product (n 3) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 1) (a 2)) (Expr.product (a 3) (a 0))) (Expr.add (Expr.product (a 1) (a 2)) (Expr.product (a 3) (a 0)))))))))
def col3Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 3)) (Expr.add (Expr.product (n 1) (q 2)) (Expr.add (Expr.product (n 2) (q 1)) (Expr.add (Expr.product (n 3) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 1) (a 2)) (Expr.product (a 3) (a 0))) (Expr.add (Expr.product (a 1) (a 2)) (Expr.product (a 3) (a 0)))))))))

theorem col3_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col3High carry a n q).value = (col3Low carry a n q).value := by
  rfl

theorem col3_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col3High carry a n q).high modulusWord) (col3Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col3High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col3High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 3) radix (hn 0 (by decide)) (hq 3 (by decide)), ⟨productBound (n 1) (q 2) radix (hn 1 (by decide)) (hq 2 (by decide)), ⟨productBound (n 2) (q 1) radix (hn 2 (by decide)) (hq 1 (by decide)), ⟨productBound (n 3) (q 0) radix (hn 3 (by decide)) (hq 0 (by decide)), ⟨True.intro, ⟨⟨productBound (a 1) (a 2) radix (ha 1 (by decide)) (ha 2 (by decide)), productBound (a 3) (a 0) radix (ha 3 (by decide)) (ha 0 (by decide))⟩, ⟨productBound (a 1) (a 2) radix (ha 1 (by decide)) (ha 2 (by decide)), productBound (a 3) (a 0) radix (ha 3 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩
  have hlit : (col3High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩⟩
  have hlitC : (col3High carry a n q).literalsBounded carry.toNat := by
    simp [col3High, Expr.literalsBounded]
  have hbound := valueBound (col3High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col3High carry a n q).products ≤ 18 := by norm_num [col3High, Expr.products]
  have hl : (col3High carry a n q).literals ≤ 1 := by norm_num [col3High, Expr.literals]
  have hcount : (col3High carry a n q).count ≤ 19 := by norm_num [col3High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col3High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col3High carry a n q) (col3Low carry a n q) carry.toNat hcount hlit
    (col3_sameValue carry a n q) hc hsum

#print axioms col3_carry

def col4High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 4)) (Expr.add (Expr.product (n 1) (q 3)) (Expr.add (Expr.product (n 2) (q 2)) (Expr.add (Expr.product (n 3) (q 1)) (Expr.add (Expr.product (n 4) (q 0)) (Expr.add (Expr.product (a 2) (a 2)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 1) (a 3)) (Expr.product (a 4) (a 0))) (Expr.add (Expr.product (a 1) (a 3)) (Expr.product (a 4) (a 0)))))))))))
def col4Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 4)) (Expr.add (Expr.product (n 1) (q 3)) (Expr.add (Expr.product (n 2) (q 2)) (Expr.add (Expr.product (n 3) (q 1)) (Expr.add (Expr.product (n 4) (q 0)) (Expr.add (Expr.product (a 2) (a 2)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 1) (a 3)) (Expr.product (a 4) (a 0))) (Expr.add (Expr.product (a 1) (a 3)) (Expr.product (a 4) (a 0)))))))))))

theorem col4_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col4High carry a n q).value = (col4Low carry a n q).value := by
  rfl

theorem col4_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col4High carry a n q).high modulusWord) (col4Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col4High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col4High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 4) radix (hn 0 (by decide)) (hq 4 (by decide)), ⟨productBound (n 1) (q 3) radix (hn 1 (by decide)) (hq 3 (by decide)), ⟨productBound (n 2) (q 2) radix (hn 2 (by decide)) (hq 2 (by decide)), ⟨productBound (n 3) (q 1) radix (hn 3 (by decide)) (hq 1 (by decide)), ⟨productBound (n 4) (q 0) radix (hn 4 (by decide)) (hq 0 (by decide)), ⟨productBound (a 2) (a 2) radix (ha 2 (by decide)) (ha 2 (by decide)), ⟨True.intro, ⟨⟨productBound (a 1) (a 3) radix (ha 1 (by decide)) (ha 3 (by decide)), productBound (a 4) (a 0) radix (ha 4 (by decide)) (ha 0 (by decide))⟩, ⟨productBound (a 1) (a 3) radix (ha 1 (by decide)) (ha 3 (by decide)), productBound (a 4) (a 0) radix (ha 4 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlit : (col4High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlitC : (col4High carry a n q).literalsBounded carry.toNat := by
    simp [col4High, Expr.literalsBounded]
  have hbound := valueBound (col4High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col4High carry a n q).products ≤ 18 := by norm_num [col4High, Expr.products]
  have hl : (col4High carry a n q).literals ≤ 1 := by norm_num [col4High, Expr.literals]
  have hcount : (col4High carry a n q).count ≤ 19 := by norm_num [col4High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col4High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col4High carry a n q) (col4Low carry a n q) carry.toNat hcount hlit
    (col4_sameValue carry a n q) hc hsum

#print axioms col4_carry

def col5High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 5)) (Expr.add (Expr.product (n 1) (q 4)) (Expr.add (Expr.product (n 2) (q 3)) (Expr.add (Expr.product (n 3) (q 2)) (Expr.add (Expr.product (n 4) (q 1)) (Expr.add (Expr.product (n 5) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 2) (a 3)) (Expr.add (Expr.product (a 1) (a 4)) (Expr.product (a 5) (a 0)))) (Expr.add (Expr.product (a 2) (a 3)) (Expr.add (Expr.product (a 1) (a 4)) (Expr.product (a 5) (a 0))))))))))))
def col5Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 5)) (Expr.add (Expr.product (n 1) (q 4)) (Expr.add (Expr.product (n 2) (q 3)) (Expr.add (Expr.product (n 3) (q 2)) (Expr.add (Expr.product (n 4) (q 1)) (Expr.add (Expr.product (n 5) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 2) (a 3)) (Expr.add (Expr.product (a 1) (a 4)) (Expr.product (a 5) (a 0)))) (Expr.add (Expr.product (a 2) (a 3)) (Expr.add (Expr.product (a 1) (a 4)) (Expr.product (a 5) (a 0))))))))))))

theorem col5_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col5High carry a n q).value = (col5Low carry a n q).value := by
  rfl

theorem col5_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col5High carry a n q).high modulusWord) (col5Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col5High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col5High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 5) radix (hn 0 (by decide)) (hq 5 (by decide)), ⟨productBound (n 1) (q 4) radix (hn 1 (by decide)) (hq 4 (by decide)), ⟨productBound (n 2) (q 3) radix (hn 2 (by decide)) (hq 3 (by decide)), ⟨productBound (n 3) (q 2) radix (hn 3 (by decide)) (hq 2 (by decide)), ⟨productBound (n 4) (q 1) radix (hn 4 (by decide)) (hq 1 (by decide)), ⟨productBound (n 5) (q 0) radix (hn 5 (by decide)) (hq 0 (by decide)), ⟨True.intro, ⟨⟨productBound (a 2) (a 3) radix (ha 2 (by decide)) (ha 3 (by decide)), ⟨productBound (a 1) (a 4) radix (ha 1 (by decide)) (ha 4 (by decide)), productBound (a 5) (a 0) radix (ha 5 (by decide)) (ha 0 (by decide))⟩⟩, ⟨productBound (a 2) (a 3) radix (ha 2 (by decide)) (ha 3 (by decide)), ⟨productBound (a 1) (a 4) radix (ha 1 (by decide)) (ha 4 (by decide)), productBound (a 5) (a 0) radix (ha 5 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlit : (col5High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨⟨True.intro, ⟨True.intro, True.intro⟩⟩, ⟨True.intro, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlitC : (col5High carry a n q).literalsBounded carry.toNat := by
    simp [col5High, Expr.literalsBounded]
  have hbound := valueBound (col5High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col5High carry a n q).products ≤ 18 := by norm_num [col5High, Expr.products]
  have hl : (col5High carry a n q).literals ≤ 1 := by norm_num [col5High, Expr.literals]
  have hcount : (col5High carry a n q).count ≤ 19 := by norm_num [col5High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col5High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col5High carry a n q) (col5Low carry a n q) carry.toNat hcount hlit
    (col5_sameValue carry a n q) hc hsum

#print axioms col5_carry

def col6High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 6)) (Expr.add (Expr.product (n 1) (q 5)) (Expr.add (Expr.product (n 2) (q 4)) (Expr.add (Expr.product (n 3) (q 3)) (Expr.add (Expr.product (n 4) (q 2)) (Expr.add (Expr.product (n 5) (q 1)) (Expr.add (Expr.product (n 6) (q 0)) (Expr.add (Expr.product (a 3) (a 3)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 2) (a 4)) (Expr.add (Expr.product (a 1) (a 5)) (Expr.product (a 6) (a 0)))) (Expr.add (Expr.product (a 2) (a 4)) (Expr.add (Expr.product (a 1) (a 5)) (Expr.product (a 6) (a 0))))))))))))))
def col6Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 6)) (Expr.add (Expr.product (n 1) (q 5)) (Expr.add (Expr.product (n 2) (q 4)) (Expr.add (Expr.product (n 3) (q 3)) (Expr.add (Expr.product (n 4) (q 2)) (Expr.add (Expr.product (n 5) (q 1)) (Expr.add (Expr.product (n 6) (q 0)) (Expr.add (Expr.product (a 3) (a 3)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 2) (a 4)) (Expr.add (Expr.product (a 1) (a 5)) (Expr.product (a 6) (a 0)))) (Expr.add (Expr.product (a 2) (a 4)) (Expr.add (Expr.product (a 1) (a 5)) (Expr.product (a 6) (a 0))))))))))))))

theorem col6_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col6High carry a n q).value = (col6Low carry a n q).value := by
  rfl

theorem col6_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col6High carry a n q).high modulusWord) (col6Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col6High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col6High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 6) radix (hn 0 (by decide)) (hq 6 (by decide)), ⟨productBound (n 1) (q 5) radix (hn 1 (by decide)) (hq 5 (by decide)), ⟨productBound (n 2) (q 4) radix (hn 2 (by decide)) (hq 4 (by decide)), ⟨productBound (n 3) (q 3) radix (hn 3 (by decide)) (hq 3 (by decide)), ⟨productBound (n 4) (q 2) radix (hn 4 (by decide)) (hq 2 (by decide)), ⟨productBound (n 5) (q 1) radix (hn 5 (by decide)) (hq 1 (by decide)), ⟨productBound (n 6) (q 0) radix (hn 6 (by decide)) (hq 0 (by decide)), ⟨productBound (a 3) (a 3) radix (ha 3 (by decide)) (ha 3 (by decide)), ⟨True.intro, ⟨⟨productBound (a 2) (a 4) radix (ha 2 (by decide)) (ha 4 (by decide)), ⟨productBound (a 1) (a 5) radix (ha 1 (by decide)) (ha 5 (by decide)), productBound (a 6) (a 0) radix (ha 6 (by decide)) (ha 0 (by decide))⟩⟩, ⟨productBound (a 2) (a 4) radix (ha 2 (by decide)) (ha 4 (by decide)), ⟨productBound (a 1) (a 5) radix (ha 1 (by decide)) (ha 5 (by decide)), productBound (a 6) (a 0) radix (ha 6 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlit : (col6High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨⟨True.intro, ⟨True.intro, True.intro⟩⟩, ⟨True.intro, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlitC : (col6High carry a n q).literalsBounded carry.toNat := by
    simp [col6High, Expr.literalsBounded]
  have hbound := valueBound (col6High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col6High carry a n q).products ≤ 18 := by norm_num [col6High, Expr.products]
  have hl : (col6High carry a n q).literals ≤ 1 := by norm_num [col6High, Expr.literals]
  have hcount : (col6High carry a n q).count ≤ 19 := by norm_num [col6High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col6High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col6High carry a n q) (col6Low carry a n q) carry.toNat hcount hlit
    (col6_sameValue carry a n q) hc hsum

#print axioms col6_carry

def col7High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 7)) (Expr.add (Expr.product (n 1) (q 6)) (Expr.add (Expr.product (n 2) (q 5)) (Expr.add (Expr.product (n 3) (q 4)) (Expr.add (Expr.product (n 4) (q 3)) (Expr.add (Expr.product (n 5) (q 2)) (Expr.add (Expr.product (n 6) (q 1)) (Expr.add (Expr.product (n 7) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 3) (a 4)) (Expr.add (Expr.product (a 2) (a 5)) (Expr.add (Expr.product (a 1) (a 6)) (Expr.product (a 7) (a 0))))) (Expr.add (Expr.product (a 3) (a 4)) (Expr.add (Expr.product (a 2) (a 5)) (Expr.add (Expr.product (a 1) (a 6)) (Expr.product (a 7) (a 0)))))))))))))))
def col7Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 7)) (Expr.add (Expr.product (n 1) (q 6)) (Expr.add (Expr.product (n 2) (q 5)) (Expr.add (Expr.product (n 3) (q 4)) (Expr.add (Expr.product (n 4) (q 3)) (Expr.add (Expr.product (n 5) (q 2)) (Expr.add (Expr.product (n 6) (q 1)) (Expr.add (Expr.product (n 7) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 3) (a 4)) (Expr.add (Expr.product (a 2) (a 5)) (Expr.add (Expr.product (a 1) (a 6)) (Expr.product (a 7) (a 0))))) (Expr.add (Expr.product (a 3) (a 4)) (Expr.add (Expr.product (a 2) (a 5)) (Expr.add (Expr.product (a 1) (a 6)) (Expr.product (a 7) (a 0)))))))))))))))

theorem col7_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col7High carry a n q).value = (col7Low carry a n q).value := by
  rfl

theorem col7_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col7High carry a n q).high modulusWord) (col7Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col7High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col7High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 7) radix (hn 0 (by decide)) (hq 7 (by decide)), ⟨productBound (n 1) (q 6) radix (hn 1 (by decide)) (hq 6 (by decide)), ⟨productBound (n 2) (q 5) radix (hn 2 (by decide)) (hq 5 (by decide)), ⟨productBound (n 3) (q 4) radix (hn 3 (by decide)) (hq 4 (by decide)), ⟨productBound (n 4) (q 3) radix (hn 4 (by decide)) (hq 3 (by decide)), ⟨productBound (n 5) (q 2) radix (hn 5 (by decide)) (hq 2 (by decide)), ⟨productBound (n 6) (q 1) radix (hn 6 (by decide)) (hq 1 (by decide)), ⟨productBound (n 7) (q 0) radix (hn 7 (by decide)) (hq 0 (by decide)), ⟨True.intro, ⟨⟨productBound (a 3) (a 4) radix (ha 3 (by decide)) (ha 4 (by decide)), ⟨productBound (a 2) (a 5) radix (ha 2 (by decide)) (ha 5 (by decide)), ⟨productBound (a 1) (a 6) radix (ha 1 (by decide)) (ha 6 (by decide)), productBound (a 7) (a 0) radix (ha 7 (by decide)) (ha 0 (by decide))⟩⟩⟩, ⟨productBound (a 3) (a 4) radix (ha 3 (by decide)) (ha 4 (by decide)), ⟨productBound (a 2) (a 5) radix (ha 2 (by decide)) (ha 5 (by decide)), ⟨productBound (a 1) (a 6) radix (ha 1 (by decide)) (ha 6 (by decide)), productBound (a 7) (a 0) radix (ha 7 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlit : (col7High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨⟨True.intro, ⟨True.intro, ⟨True.intro, True.intro⟩⟩⟩, ⟨True.intro, ⟨True.intro, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlitC : (col7High carry a n q).literalsBounded carry.toNat := by
    simp [col7High, Expr.literalsBounded]
  have hbound := valueBound (col7High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col7High carry a n q).products ≤ 18 := by norm_num [col7High, Expr.products]
  have hl : (col7High carry a n q).literals ≤ 1 := by norm_num [col7High, Expr.literals]
  have hcount : (col7High carry a n q).count ≤ 19 := by norm_num [col7High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col7High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col7High carry a n q) (col7Low carry a n q) carry.toNat hcount hlit
    (col7_sameValue carry a n q) hc hsum

#print axioms col7_carry

def col8High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 8)) (Expr.add (Expr.product (n 1) (q 7)) (Expr.add (Expr.product (n 2) (q 6)) (Expr.add (Expr.product (n 3) (q 5)) (Expr.add (Expr.product (n 4) (q 4)) (Expr.add (Expr.product (n 5) (q 3)) (Expr.add (Expr.product (n 6) (q 2)) (Expr.add (Expr.product (n 7) (q 1)) (Expr.add (Expr.product (n 8) (q 0)) (Expr.add (Expr.product (a 4) (a 4)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 3) (a 5)) (Expr.add (Expr.product (a 2) (a 6)) (Expr.add (Expr.product (a 1) (a 7)) (Expr.product (a 8) (a 0))))) (Expr.add (Expr.product (a 3) (a 5)) (Expr.add (Expr.product (a 2) (a 6)) (Expr.add (Expr.product (a 1) (a 7)) (Expr.product (a 8) (a 0)))))))))))))))))
def col8Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 8)) (Expr.add (Expr.product (n 1) (q 7)) (Expr.add (Expr.product (n 2) (q 6)) (Expr.add (Expr.product (n 3) (q 5)) (Expr.add (Expr.product (n 4) (q 4)) (Expr.add (Expr.product (n 5) (q 3)) (Expr.add (Expr.product (n 6) (q 2)) (Expr.add (Expr.product (n 7) (q 1)) (Expr.add (Expr.product (n 8) (q 0)) (Expr.add (Expr.product (a 4) (a 4)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 3) (a 5)) (Expr.add (Expr.product (a 2) (a 6)) (Expr.add (Expr.product (a 1) (a 7)) (Expr.product (a 8) (a 0))))) (Expr.add (Expr.product (a 3) (a 5)) (Expr.add (Expr.product (a 2) (a 6)) (Expr.add (Expr.product (a 1) (a 7)) (Expr.product (a 8) (a 0)))))))))))))))))

theorem col8_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col8High carry a n q).value = (col8Low carry a n q).value := by
  rfl

theorem col8_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col8High carry a n q).high modulusWord) (col8Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col8High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col8High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 8) radix (hn 0 (by decide)) (hq 8 (by decide)), ⟨productBound (n 1) (q 7) radix (hn 1 (by decide)) (hq 7 (by decide)), ⟨productBound (n 2) (q 6) radix (hn 2 (by decide)) (hq 6 (by decide)), ⟨productBound (n 3) (q 5) radix (hn 3 (by decide)) (hq 5 (by decide)), ⟨productBound (n 4) (q 4) radix (hn 4 (by decide)) (hq 4 (by decide)), ⟨productBound (n 5) (q 3) radix (hn 5 (by decide)) (hq 3 (by decide)), ⟨productBound (n 6) (q 2) radix (hn 6 (by decide)) (hq 2 (by decide)), ⟨productBound (n 7) (q 1) radix (hn 7 (by decide)) (hq 1 (by decide)), ⟨productBound (n 8) (q 0) radix (hn 8 (by decide)) (hq 0 (by decide)), ⟨productBound (a 4) (a 4) radix (ha 4 (by decide)) (ha 4 (by decide)), ⟨True.intro, ⟨⟨productBound (a 3) (a 5) radix (ha 3 (by decide)) (ha 5 (by decide)), ⟨productBound (a 2) (a 6) radix (ha 2 (by decide)) (ha 6 (by decide)), ⟨productBound (a 1) (a 7) radix (ha 1 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 0) radix (ha 8 (by decide)) (ha 0 (by decide))⟩⟩⟩, ⟨productBound (a 3) (a 5) radix (ha 3 (by decide)) (ha 5 (by decide)), ⟨productBound (a 2) (a 6) radix (ha 2 (by decide)) (ha 6 (by decide)), ⟨productBound (a 1) (a 7) radix (ha 1 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 0) radix (ha 8 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlit : (col8High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨⟨True.intro, ⟨True.intro, ⟨True.intro, True.intro⟩⟩⟩, ⟨True.intro, ⟨True.intro, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlitC : (col8High carry a n q).literalsBounded carry.toNat := by
    simp [col8High, Expr.literalsBounded]
  have hbound := valueBound (col8High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col8High carry a n q).products ≤ 18 := by norm_num [col8High, Expr.products]
  have hl : (col8High carry a n q).literals ≤ 1 := by norm_num [col8High, Expr.literals]
  have hcount : (col8High carry a n q).count ≤ 19 := by norm_num [col8High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col8High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col8High carry a n q) (col8Low carry a n q) carry.toNat hcount hlit
    (col8_sameValue carry a n q) hc hsum

#print axioms col8_carry

def col9High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 8)) (Expr.add (Expr.product (n 2) (q 7)) (Expr.add (Expr.product (n 3) (q 6)) (Expr.add (Expr.product (n 4) (q 5)) (Expr.add (Expr.product (n 5) (q 4)) (Expr.add (Expr.product (n 6) (q 3)) (Expr.add (Expr.product (n 7) (q 2)) (Expr.add (Expr.product (n 8) (q 1)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 4) (a 5)) (Expr.add (Expr.product (a 3) (a 6)) (Expr.add (Expr.product (a 2) (a 7)) (Expr.product (a 8) (a 1))))) (Expr.add (Expr.product (a 4) (a 5)) (Expr.add (Expr.product (a 3) (a 6)) (Expr.add (Expr.product (a 2) (a 7)) (Expr.product (a 8) (a 1)))))))))))))))
def col9Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 8)) (Expr.add (Expr.product (n 2) (q 7)) (Expr.add (Expr.product (n 3) (q 6)) (Expr.add (Expr.product (n 4) (q 5)) (Expr.add (Expr.product (n 5) (q 4)) (Expr.add (Expr.product (n 6) (q 3)) (Expr.add (Expr.product (n 7) (q 2)) (Expr.add (Expr.product (n 8) (q 1)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 4) (a 5)) (Expr.add (Expr.product (a 3) (a 6)) (Expr.add (Expr.product (a 2) (a 7)) (Expr.product (a 8) (a 1))))) (Expr.add (Expr.product (a 4) (a 5)) (Expr.add (Expr.product (a 3) (a 6)) (Expr.add (Expr.product (a 2) (a 7)) (Expr.product (a 8) (a 1)))))))))))))))

theorem col9_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col9High carry a n q).value = (col9Low carry a n q).value := by
  rfl

theorem col9_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col9High carry a n q).high modulusWord) (col9Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col9High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col9High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 1) (q 8) radix (hn 1 (by decide)) (hq 8 (by decide)), ⟨productBound (n 2) (q 7) radix (hn 2 (by decide)) (hq 7 (by decide)), ⟨productBound (n 3) (q 6) radix (hn 3 (by decide)) (hq 6 (by decide)), ⟨productBound (n 4) (q 5) radix (hn 4 (by decide)) (hq 5 (by decide)), ⟨productBound (n 5) (q 4) radix (hn 5 (by decide)) (hq 4 (by decide)), ⟨productBound (n 6) (q 3) radix (hn 6 (by decide)) (hq 3 (by decide)), ⟨productBound (n 7) (q 2) radix (hn 7 (by decide)) (hq 2 (by decide)), ⟨productBound (n 8) (q 1) radix (hn 8 (by decide)) (hq 1 (by decide)), ⟨True.intro, ⟨⟨productBound (a 4) (a 5) radix (ha 4 (by decide)) (ha 5 (by decide)), ⟨productBound (a 3) (a 6) radix (ha 3 (by decide)) (ha 6 (by decide)), ⟨productBound (a 2) (a 7) radix (ha 2 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 1) radix (ha 8 (by decide)) (ha 1 (by decide))⟩⟩⟩, ⟨productBound (a 4) (a 5) radix (ha 4 (by decide)) (ha 5 (by decide)), ⟨productBound (a 3) (a 6) radix (ha 3 (by decide)) (ha 6 (by decide)), ⟨productBound (a 2) (a 7) radix (ha 2 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 1) radix (ha 8 (by decide)) (ha 1 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlit : (col9High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨⟨True.intro, ⟨True.intro, ⟨True.intro, True.intro⟩⟩⟩, ⟨True.intro, ⟨True.intro, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlitC : (col9High carry a n q).literalsBounded carry.toNat := by
    simp [col9High, Expr.literalsBounded]
  have hbound := valueBound (col9High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col9High carry a n q).products ≤ 18 := by norm_num [col9High, Expr.products]
  have hl : (col9High carry a n q).literals ≤ 1 := by norm_num [col9High, Expr.literals]
  have hcount : (col9High carry a n q).count ≤ 19 := by norm_num [col9High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col9High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col9High carry a n q) (col9Low carry a n q) carry.toNat hcount hlit
    (col9_sameValue carry a n q) hc hsum

#print axioms col9_carry

def col10High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 2) (q 8)) (Expr.add (Expr.product (n 3) (q 7)) (Expr.add (Expr.product (n 4) (q 6)) (Expr.add (Expr.product (n 5) (q 5)) (Expr.add (Expr.product (n 6) (q 4)) (Expr.add (Expr.product (n 7) (q 3)) (Expr.add (Expr.product (n 8) (q 2)) (Expr.add (Expr.product (a 5) (a 5)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 4) (a 6)) (Expr.add (Expr.product (a 3) (a 7)) (Expr.product (a 8) (a 2)))) (Expr.add (Expr.product (a 4) (a 6)) (Expr.add (Expr.product (a 3) (a 7)) (Expr.product (a 8) (a 2))))))))))))))
def col10Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 2) (q 8)) (Expr.add (Expr.product (n 3) (q 7)) (Expr.add (Expr.product (n 4) (q 6)) (Expr.add (Expr.product (n 5) (q 5)) (Expr.add (Expr.product (n 6) (q 4)) (Expr.add (Expr.product (n 7) (q 3)) (Expr.add (Expr.product (n 8) (q 2)) (Expr.add (Expr.product (a 5) (a 5)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 4) (a 6)) (Expr.add (Expr.product (a 3) (a 7)) (Expr.product (a 8) (a 2)))) (Expr.add (Expr.product (a 4) (a 6)) (Expr.add (Expr.product (a 3) (a 7)) (Expr.product (a 8) (a 2))))))))))))))

theorem col10_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col10High carry a n q).value = (col10Low carry a n q).value := by
  rfl

theorem col10_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col10High carry a n q).high modulusWord) (col10Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col10High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col10High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 2) (q 8) radix (hn 2 (by decide)) (hq 8 (by decide)), ⟨productBound (n 3) (q 7) radix (hn 3 (by decide)) (hq 7 (by decide)), ⟨productBound (n 4) (q 6) radix (hn 4 (by decide)) (hq 6 (by decide)), ⟨productBound (n 5) (q 5) radix (hn 5 (by decide)) (hq 5 (by decide)), ⟨productBound (n 6) (q 4) radix (hn 6 (by decide)) (hq 4 (by decide)), ⟨productBound (n 7) (q 3) radix (hn 7 (by decide)) (hq 3 (by decide)), ⟨productBound (n 8) (q 2) radix (hn 8 (by decide)) (hq 2 (by decide)), ⟨productBound (a 5) (a 5) radix (ha 5 (by decide)) (ha 5 (by decide)), ⟨True.intro, ⟨⟨productBound (a 4) (a 6) radix (ha 4 (by decide)) (ha 6 (by decide)), ⟨productBound (a 3) (a 7) radix (ha 3 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 2) radix (ha 8 (by decide)) (ha 2 (by decide))⟩⟩, ⟨productBound (a 4) (a 6) radix (ha 4 (by decide)) (ha 6 (by decide)), ⟨productBound (a 3) (a 7) radix (ha 3 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 2) radix (ha 8 (by decide)) (ha 2 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlit : (col10High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨⟨True.intro, ⟨True.intro, True.intro⟩⟩, ⟨True.intro, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlitC : (col10High carry a n q).literalsBounded carry.toNat := by
    simp [col10High, Expr.literalsBounded]
  have hbound := valueBound (col10High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col10High carry a n q).products ≤ 18 := by norm_num [col10High, Expr.products]
  have hl : (col10High carry a n q).literals ≤ 1 := by norm_num [col10High, Expr.literals]
  have hcount : (col10High carry a n q).count ≤ 19 := by norm_num [col10High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col10High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col10High carry a n q) (col10Low carry a n q) carry.toNat hcount hlit
    (col10_sameValue carry a n q) hc hsum

#print axioms col10_carry

def col11High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 3) (q 8)) (Expr.add (Expr.product (n 4) (q 7)) (Expr.add (Expr.product (n 5) (q 6)) (Expr.add (Expr.product (n 6) (q 5)) (Expr.add (Expr.product (n 7) (q 4)) (Expr.add (Expr.product (n 8) (q 3)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 5) (a 6)) (Expr.add (Expr.product (a 4) (a 7)) (Expr.product (a 8) (a 3)))) (Expr.add (Expr.product (a 5) (a 6)) (Expr.add (Expr.product (a 4) (a 7)) (Expr.product (a 8) (a 3))))))))))))
def col11Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 3) (q 8)) (Expr.add (Expr.product (n 4) (q 7)) (Expr.add (Expr.product (n 5) (q 6)) (Expr.add (Expr.product (n 6) (q 5)) (Expr.add (Expr.product (n 7) (q 4)) (Expr.add (Expr.product (n 8) (q 3)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 5) (a 6)) (Expr.add (Expr.product (a 4) (a 7)) (Expr.product (a 8) (a 3)))) (Expr.add (Expr.product (a 5) (a 6)) (Expr.add (Expr.product (a 4) (a 7)) (Expr.product (a 8) (a 3))))))))))))

theorem col11_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col11High carry a n q).value = (col11Low carry a n q).value := by
  rfl

theorem col11_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col11High carry a n q).high modulusWord) (col11Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col11High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col11High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 3) (q 8) radix (hn 3 (by decide)) (hq 8 (by decide)), ⟨productBound (n 4) (q 7) radix (hn 4 (by decide)) (hq 7 (by decide)), ⟨productBound (n 5) (q 6) radix (hn 5 (by decide)) (hq 6 (by decide)), ⟨productBound (n 6) (q 5) radix (hn 6 (by decide)) (hq 5 (by decide)), ⟨productBound (n 7) (q 4) radix (hn 7 (by decide)) (hq 4 (by decide)), ⟨productBound (n 8) (q 3) radix (hn 8 (by decide)) (hq 3 (by decide)), ⟨True.intro, ⟨⟨productBound (a 5) (a 6) radix (ha 5 (by decide)) (ha 6 (by decide)), ⟨productBound (a 4) (a 7) radix (ha 4 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 3) radix (ha 8 (by decide)) (ha 3 (by decide))⟩⟩, ⟨productBound (a 5) (a 6) radix (ha 5 (by decide)) (ha 6 (by decide)), ⟨productBound (a 4) (a 7) radix (ha 4 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 3) radix (ha 8 (by decide)) (ha 3 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlit : (col11High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨⟨True.intro, ⟨True.intro, True.intro⟩⟩, ⟨True.intro, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlitC : (col11High carry a n q).literalsBounded carry.toNat := by
    simp [col11High, Expr.literalsBounded]
  have hbound := valueBound (col11High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col11High carry a n q).products ≤ 18 := by norm_num [col11High, Expr.products]
  have hl : (col11High carry a n q).literals ≤ 1 := by norm_num [col11High, Expr.literals]
  have hcount : (col11High carry a n q).count ≤ 19 := by norm_num [col11High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col11High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col11High carry a n q) (col11Low carry a n q) carry.toNat hcount hlit
    (col11_sameValue carry a n q) hc hsum

#print axioms col11_carry

def col12High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 4) (q 8)) (Expr.add (Expr.product (n 5) (q 7)) (Expr.add (Expr.product (n 6) (q 6)) (Expr.add (Expr.product (n 7) (q 5)) (Expr.add (Expr.product (n 8) (q 4)) (Expr.add (Expr.product (a 6) (a 6)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 5) (a 7)) (Expr.product (a 8) (a 4))) (Expr.add (Expr.product (a 5) (a 7)) (Expr.product (a 8) (a 4)))))))))))
def col12Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 4) (q 8)) (Expr.add (Expr.product (n 5) (q 7)) (Expr.add (Expr.product (n 6) (q 6)) (Expr.add (Expr.product (n 7) (q 5)) (Expr.add (Expr.product (n 8) (q 4)) (Expr.add (Expr.product (a 6) (a 6)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 5) (a 7)) (Expr.product (a 8) (a 4))) (Expr.add (Expr.product (a 5) (a 7)) (Expr.product (a 8) (a 4)))))))))))

theorem col12_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col12High carry a n q).value = (col12Low carry a n q).value := by
  rfl

theorem col12_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col12High carry a n q).high modulusWord) (col12Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col12High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col12High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 4) (q 8) radix (hn 4 (by decide)) (hq 8 (by decide)), ⟨productBound (n 5) (q 7) radix (hn 5 (by decide)) (hq 7 (by decide)), ⟨productBound (n 6) (q 6) radix (hn 6 (by decide)) (hq 6 (by decide)), ⟨productBound (n 7) (q 5) radix (hn 7 (by decide)) (hq 5 (by decide)), ⟨productBound (n 8) (q 4) radix (hn 8 (by decide)) (hq 4 (by decide)), ⟨productBound (a 6) (a 6) radix (ha 6 (by decide)) (ha 6 (by decide)), ⟨True.intro, ⟨⟨productBound (a 5) (a 7) radix (ha 5 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 4) radix (ha 8 (by decide)) (ha 4 (by decide))⟩, ⟨productBound (a 5) (a 7) radix (ha 5 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 4) radix (ha 8 (by decide)) (ha 4 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlit : (col12High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hlitC : (col12High carry a n q).literalsBounded carry.toNat := by
    simp [col12High, Expr.literalsBounded]
  have hbound := valueBound (col12High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col12High carry a n q).products ≤ 18 := by norm_num [col12High, Expr.products]
  have hl : (col12High carry a n q).literals ≤ 1 := by norm_num [col12High, Expr.literals]
  have hcount : (col12High carry a n q).count ≤ 19 := by norm_num [col12High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col12High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col12High carry a n q) (col12Low carry a n q) carry.toNat hcount hlit
    (col12_sameValue carry a n q) hc hsum

#print axioms col12_carry

def col13High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 5) (q 8)) (Expr.add (Expr.product (n 6) (q 7)) (Expr.add (Expr.product (n 7) (q 6)) (Expr.add (Expr.product (n 8) (q 5)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 6) (a 7)) (Expr.product (a 8) (a 5))) (Expr.add (Expr.product (a 6) (a 7)) (Expr.product (a 8) (a 5)))))))))
def col13Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 5) (q 8)) (Expr.add (Expr.product (n 6) (q 7)) (Expr.add (Expr.product (n 7) (q 6)) (Expr.add (Expr.product (n 8) (q 5)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 6) (a 7)) (Expr.product (a 8) (a 5))) (Expr.add (Expr.product (a 6) (a 7)) (Expr.product (a 8) (a 5)))))))))

theorem col13_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col13High carry a n q).value = (col13Low carry a n q).value := by
  rfl

theorem col13_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col13High carry a n q).high modulusWord) (col13Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col13High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col13High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 5) (q 8) radix (hn 5 (by decide)) (hq 8 (by decide)), ⟨productBound (n 6) (q 7) radix (hn 6 (by decide)) (hq 7 (by decide)), ⟨productBound (n 7) (q 6) radix (hn 7 (by decide)) (hq 6 (by decide)), ⟨productBound (n 8) (q 5) radix (hn 8 (by decide)) (hq 5 (by decide)), ⟨True.intro, ⟨⟨productBound (a 6) (a 7) radix (ha 6 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 5) radix (ha 8 (by decide)) (ha 5 (by decide))⟩, ⟨productBound (a 6) (a 7) radix (ha 6 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 5) radix (ha 8 (by decide)) (ha 5 (by decide))⟩⟩⟩⟩⟩⟩⟩
  have hlit : (col13High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩⟩
  have hlitC : (col13High carry a n q).literalsBounded carry.toNat := by
    simp [col13High, Expr.literalsBounded]
  have hbound := valueBound (col13High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col13High carry a n q).products ≤ 18 := by norm_num [col13High, Expr.products]
  have hl : (col13High carry a n q).literals ≤ 1 := by norm_num [col13High, Expr.literals]
  have hcount : (col13High carry a n q).count ≤ 19 := by norm_num [col13High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col13High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col13High carry a n q) (col13Low carry a n q) carry.toNat hcount hlit
    (col13_sameValue carry a n q) hc hsum

#print axioms col13_carry

def col14High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 6) (q 8)) (Expr.add (Expr.product (n 7) (q 7)) (Expr.add (Expr.product (n 8) (q 6)) (Expr.add (Expr.product (a 7) (a 7)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 8) (a 6)) (Expr.product (a 8) (a 6))))))))
def col14Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 6) (q 8)) (Expr.add (Expr.product (n 7) (q 7)) (Expr.add (Expr.product (n 8) (q 6)) (Expr.add (Expr.product (a 7) (a 7)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 8) (a 6)) (Expr.product (a 8) (a 6))))))))

theorem col14_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col14High carry a n q).value = (col14Low carry a n q).value := by
  rfl

theorem col14_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col14High carry a n q).high modulusWord) (col14Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col14High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col14High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 6) (q 8) radix (hn 6 (by decide)) (hq 8 (by decide)), ⟨productBound (n 7) (q 7) radix (hn 7 (by decide)) (hq 7 (by decide)), ⟨productBound (n 8) (q 6) radix (hn 8 (by decide)) (hq 6 (by decide)), ⟨productBound (a 7) (a 7) radix (ha 7 (by decide)) (ha 7 (by decide)), ⟨True.intro, ⟨productBound (a 8) (a 6) radix (ha 8 (by decide)) (ha 6 (by decide)), productBound (a 8) (a 6) radix (ha 8 (by decide)) (ha 6 (by decide))⟩⟩⟩⟩⟩⟩
  have hlit : (col14High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨True.intro, True.intro⟩⟩⟩⟩⟩⟩
  have hlitC : (col14High carry a n q).literalsBounded carry.toNat := by
    simp [col14High, Expr.literalsBounded]
  have hbound := valueBound (col14High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col14High carry a n q).products ≤ 18 := by norm_num [col14High, Expr.products]
  have hl : (col14High carry a n q).literals ≤ 1 := by norm_num [col14High, Expr.literals]
  have hcount : (col14High carry a n q).count ≤ 19 := by norm_num [col14High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col14High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col14High carry a n q) (col14Low carry a n q) carry.toNat hcount hlit
    (col14_sameValue carry a n q) hc hsum

#print axioms col14_carry

def col15High (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 7) (q 8)) (Expr.add (Expr.product (n 8) (q 7)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 8) (a 7)) (Expr.product (a 8) (a 7))))))
def col15Low (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 7) (q 8)) (Expr.add (Expr.product (n 8) (q 7)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 8) (a 7)) (Expr.product (a 8) (a 7))))))

theorem col15_sameValue (carry : UInt256) (a n q : Nat → UInt256) : (col15High carry a n q).value = (col15Low carry a n q).value := by
  rfl

theorem col15_carry (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (carryWord ((col15High carry a n q).high modulusWord) (col15Low carry a n q).low modulusWord
      (UInt256.ofNat 244) (UInt256.ofNat 12)).toNat = (col15High carry a n q).value / radix := by
  have hcP : carry.toNat ≤ residueModulus-1 := by
    have hh := carryReductionRedundant 244 carry.toNat (by decide) hc
    omega
  have hproducts : (col15High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 7) (q 8) radix (hn 7 (by decide)) (hq 8 (by decide)), ⟨productBound (n 8) (q 7) radix (hn 8 (by decide)) (hq 7 (by decide)), ⟨True.intro, ⟨productBound (a 8) (a 7) radix (ha 8 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 7) radix (ha 8 (by decide)) (ha 7 (by decide))⟩⟩⟩⟩
  have hlit : (col15High carry a n q).literalsBounded (residueModulus-1) := by
    exact ⟨True.intro, ⟨True.intro, ⟨hcP, ⟨True.intro, True.intro⟩⟩⟩⟩
  have hlitC : (col15High carry a n q).literalsBounded carry.toNat := by
    simp [col15High, Expr.literalsBounded]
  have hbound := valueBound (col15High carry a n q) ((radix-1)^2) carry.toNat hproducts hlitC
  have hp : (col15High carry a n q).products ≤ 18 := by norm_num [col15High, Expr.products]
  have hl : (col15High carry a n q).literals ≤ 1 := by norm_num [col15High, Expr.literals]
  have hcount : (col15High carry a n q).count ≤ 19 := by norm_num [col15High, Expr.count]
  have hpbound := Nat.mul_le_mul_right ((radix-1)^2) hp
  have hlbound := Nat.mul_le_mul_right carry.toNat hl
  have hsum : (col15High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by nlinarith
  exact reconstructExpressions (col15High carry a n q) (col15Low carry a n q) carry.toNat hcount hlit
    (col15_sameValue carry a n q) hc hsum

#print axioms col15_carry

end HistoricalSearch.GeneratedArithmetic
