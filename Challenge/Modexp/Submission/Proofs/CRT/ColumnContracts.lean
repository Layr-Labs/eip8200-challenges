import Challenge.Modexp.Submission.Proofs.CRT.ConcreteArithmetic
import Challenge.Modexp.Submission.Proofs.CRT.ConcreteConvolution
import Challenge.Modexp.Submission.Proofs.CRT.TailArithmetic
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace HistoricalSearch.ColumnContracts
open EvmSemantics
open HistoricalSearch.CRTColumn HistoricalSearch.ColumnExpressions
open HistoricalSearch.GeneratedArithmetic HistoricalSearch.ConcreteArithmetic
open HistoricalSearch.WordCancellation HistoricalSearch.MixedMontgomery

def col0Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col0High carry a n (col0Qs carry minv a n q)).value

theorem col0_post (carry minv : UInt256) (a n q : Nat → UInt256) :
    col0Sum carry minv a n q = (col0Pre carry a n q).value + (GeneratedColumns.col0Cancel carry modulusWord maskWord minv a n q).toNat*(n 0).toNat := by
  simp only [col0Sum, GeneratedArithmetic.col0High, col0Qs, col0Pre, Expr.value]
  norm_num
  ring

theorem col0_cancels (carry minv : UInt256) (a n q : Nat → UInt256) (N : Nat)
    (hn0 : (n 0).toNat = N % 2^244)
    (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    col0Sum carry minv a n q % 2^244 = 0 := by
  rw [col0_post, col0_cancelExpr]
  exact (maskedDigitCancels (col0Pre carry a n q).low minv 244 244
    (col0Pre carry a n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue _) hn0 hinv).2.1

#print axioms col0_cancels

theorem col0_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col0High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col0High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 0) radix (hn 0 (by decide)) (hq 0 (by decide)), productBound (a 0) (a 0) radix (ha 0 (by decide)) (ha 0 (by decide))⟩
  have hl : (GeneratedArithmetic.col0High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col0High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col0High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col0High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col0High, Expr.products]
  have hlc : (GeneratedArithmetic.col0High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col0High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col0_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 0, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col0Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col0_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col0_sumBound carry a n (col0Qs carry minv a n q) ha hn (col0_qsBound carry minv a n q hq))

#print axioms col0_carryBound

def col1Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col1High carry a n (col1Qs carry minv a n q)).value

theorem col1_post (carry minv : UInt256) (a n q : Nat → UInt256) :
    col1Sum carry minv a n q = (col1Pre carry a n q).value + (GeneratedColumns.col1Cancel carry modulusWord maskWord minv a n q).toNat*(n 0).toNat := by
  simp only [col1Sum, GeneratedArithmetic.col1High, col1Qs, col1Pre, Expr.value]
  norm_num
  ring

theorem col1_cancels (carry minv : UInt256) (a n q : Nat → UInt256) (N : Nat)
    (hn0 : (n 0).toNat = N % 2^244)
    (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    col1Sum carry minv a n q % 2^244 = 0 := by
  rw [col1_post, col1_cancelExpr]
  exact (maskedDigitCancels (col1Pre carry a n q).low minv 244 244
    (col1Pre carry a n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue _) hn0 hinv).2.1

#print axioms col1_cancels

theorem col1_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col1High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col1High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 1) radix (hn 0 (by decide)) (hq 1 (by decide)), ⟨productBound (n 1) (q 0) radix (hn 1 (by decide)) (hq 0 (by decide)), ⟨True.intro, ⟨productBound (a 1) (a 0) radix (ha 1 (by decide)) (ha 0 (by decide)), productBound (a 1) (a 0) radix (ha 1 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col1High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col1High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col1High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col1High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col1High, Expr.products]
  have hlc : (GeneratedArithmetic.col1High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col1High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col1_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 1, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col1Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col1_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col1_sumBound carry a n (col1Qs carry minv a n q) ha hn (col1_qsBound carry minv a n q hq))

#print axioms col1_carryBound

def col2Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col2High carry a n (col2Qs carry minv a n q)).value

theorem col2_post (carry minv : UInt256) (a n q : Nat → UInt256) :
    col2Sum carry minv a n q = (col2Pre carry a n q).value + (GeneratedColumns.col2Cancel carry modulusWord maskWord minv a n q).toNat*(n 0).toNat := by
  simp only [col2Sum, GeneratedArithmetic.col2High, col2Qs, col2Pre, Expr.value]
  norm_num
  ring

theorem col2_cancels (carry minv : UInt256) (a n q : Nat → UInt256) (N : Nat)
    (hn0 : (n 0).toNat = N % 2^244)
    (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    col2Sum carry minv a n q % 2^244 = 0 := by
  rw [col2_post, col2_cancelExpr]
  exact (maskedDigitCancels (col2Pre carry a n q).low minv 244 244
    (col2Pre carry a n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue _) hn0 hinv).2.1

#print axioms col2_cancels

theorem col2_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col2High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col2High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 2) radix (hn 0 (by decide)) (hq 2 (by decide)), ⟨productBound (n 1) (q 1) radix (hn 1 (by decide)) (hq 1 (by decide)), ⟨productBound (n 2) (q 0) radix (hn 2 (by decide)) (hq 0 (by decide)), ⟨productBound (a 1) (a 1) radix (ha 1 (by decide)) (ha 1 (by decide)), ⟨True.intro, ⟨productBound (a 2) (a 0) radix (ha 2 (by decide)) (ha 0 (by decide)), productBound (a 2) (a 0) radix (ha 2 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col2High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col2High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col2High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col2High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col2High, Expr.products]
  have hlc : (GeneratedArithmetic.col2High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col2High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col2_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 2, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col2Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col2_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col2_sumBound carry a n (col2Qs carry minv a n q) ha hn (col2_qsBound carry minv a n q hq))

#print axioms col2_carryBound

def col3Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col3High carry a n (col3Qs carry minv a n q)).value

theorem col3_post (carry minv : UInt256) (a n q : Nat → UInt256) :
    col3Sum carry minv a n q = (col3Pre carry a n q).value + (GeneratedColumns.col3Cancel carry modulusWord maskWord minv a n q).toNat*(n 0).toNat := by
  simp only [col3Sum, GeneratedArithmetic.col3High, col3Qs, col3Pre, Expr.value]
  norm_num
  ring

theorem col3_cancels (carry minv : UInt256) (a n q : Nat → UInt256) (N : Nat)
    (hn0 : (n 0).toNat = N % 2^244)
    (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    col3Sum carry minv a n q % 2^244 = 0 := by
  rw [col3_post, col3_cancelExpr]
  exact (maskedDigitCancels (col3Pre carry a n q).low minv 244 244
    (col3Pre carry a n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue _) hn0 hinv).2.1

#print axioms col3_cancels

theorem col3_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col3High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col3High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 3) radix (hn 0 (by decide)) (hq 3 (by decide)), ⟨productBound (n 1) (q 2) radix (hn 1 (by decide)) (hq 2 (by decide)), ⟨productBound (n 2) (q 1) radix (hn 2 (by decide)) (hq 1 (by decide)), ⟨productBound (n 3) (q 0) radix (hn 3 (by decide)) (hq 0 (by decide)), ⟨True.intro, ⟨⟨productBound (a 1) (a 2) radix (ha 1 (by decide)) (ha 2 (by decide)), productBound (a 3) (a 0) radix (ha 3 (by decide)) (ha 0 (by decide))⟩, ⟨productBound (a 1) (a 2) radix (ha 1 (by decide)) (ha 2 (by decide)), productBound (a 3) (a 0) radix (ha 3 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col3High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col3High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col3High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col3High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col3High, Expr.products]
  have hlc : (GeneratedArithmetic.col3High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col3High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col3_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 3, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col3Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col3_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col3_sumBound carry a n (col3Qs carry minv a n q) ha hn (col3_qsBound carry minv a n q hq))

#print axioms col3_carryBound

def col4Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col4High carry a n (col4Qs carry minv a n q)).value

theorem col4_post (carry minv : UInt256) (a n q : Nat → UInt256) :
    col4Sum carry minv a n q = (col4Pre carry a n q).value + (GeneratedColumns.col4Cancel carry modulusWord maskWord minv a n q).toNat*(n 0).toNat := by
  simp only [col4Sum, GeneratedArithmetic.col4High, col4Qs, col4Pre, Expr.value]
  norm_num
  ring

theorem col4_cancels (carry minv : UInt256) (a n q : Nat → UInt256) (N : Nat)
    (hn0 : (n 0).toNat = N % 2^244)
    (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    col4Sum carry minv a n q % 2^244 = 0 := by
  rw [col4_post, col4_cancelExpr]
  exact (maskedDigitCancels (col4Pre carry a n q).low minv 244 244
    (col4Pre carry a n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue _) hn0 hinv).2.1

#print axioms col4_cancels

theorem col4_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col4High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col4High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 4) radix (hn 0 (by decide)) (hq 4 (by decide)), ⟨productBound (n 1) (q 3) radix (hn 1 (by decide)) (hq 3 (by decide)), ⟨productBound (n 2) (q 2) radix (hn 2 (by decide)) (hq 2 (by decide)), ⟨productBound (n 3) (q 1) radix (hn 3 (by decide)) (hq 1 (by decide)), ⟨productBound (n 4) (q 0) radix (hn 4 (by decide)) (hq 0 (by decide)), ⟨productBound (a 2) (a 2) radix (ha 2 (by decide)) (ha 2 (by decide)), ⟨True.intro, ⟨⟨productBound (a 1) (a 3) radix (ha 1 (by decide)) (ha 3 (by decide)), productBound (a 4) (a 0) radix (ha 4 (by decide)) (ha 0 (by decide))⟩, ⟨productBound (a 1) (a 3) radix (ha 1 (by decide)) (ha 3 (by decide)), productBound (a 4) (a 0) radix (ha 4 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col4High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col4High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col4High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col4High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col4High, Expr.products]
  have hlc : (GeneratedArithmetic.col4High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col4High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col4_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 4, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col4Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col4_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col4_sumBound carry a n (col4Qs carry minv a n q) ha hn (col4_qsBound carry minv a n q hq))

#print axioms col4_carryBound

def col5Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col5High carry a n (col5Qs carry minv a n q)).value

theorem col5_post (carry minv : UInt256) (a n q : Nat → UInt256) :
    col5Sum carry minv a n q = (col5Pre carry a n q).value + (GeneratedColumns.col5Cancel carry modulusWord maskWord minv a n q).toNat*(n 0).toNat := by
  simp only [col5Sum, GeneratedArithmetic.col5High, col5Qs, col5Pre, Expr.value]
  norm_num
  ring

theorem col5_cancels (carry minv : UInt256) (a n q : Nat → UInt256) (N : Nat)
    (hn0 : (n 0).toNat = N % 2^244)
    (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    col5Sum carry minv a n q % 2^244 = 0 := by
  rw [col5_post, col5_cancelExpr]
  exact (maskedDigitCancels (col5Pre carry a n q).low minv 244 244
    (col5Pre carry a n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue _) hn0 hinv).2.1

#print axioms col5_cancels

theorem col5_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col5High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col5High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 5) radix (hn 0 (by decide)) (hq 5 (by decide)), ⟨productBound (n 1) (q 4) radix (hn 1 (by decide)) (hq 4 (by decide)), ⟨productBound (n 2) (q 3) radix (hn 2 (by decide)) (hq 3 (by decide)), ⟨productBound (n 3) (q 2) radix (hn 3 (by decide)) (hq 2 (by decide)), ⟨productBound (n 4) (q 1) radix (hn 4 (by decide)) (hq 1 (by decide)), ⟨productBound (n 5) (q 0) radix (hn 5 (by decide)) (hq 0 (by decide)), ⟨True.intro, ⟨⟨productBound (a 2) (a 3) radix (ha 2 (by decide)) (ha 3 (by decide)), ⟨productBound (a 1) (a 4) radix (ha 1 (by decide)) (ha 4 (by decide)), productBound (a 5) (a 0) radix (ha 5 (by decide)) (ha 0 (by decide))⟩⟩, ⟨productBound (a 2) (a 3) radix (ha 2 (by decide)) (ha 3 (by decide)), ⟨productBound (a 1) (a 4) radix (ha 1 (by decide)) (ha 4 (by decide)), productBound (a 5) (a 0) radix (ha 5 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col5High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col5High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col5High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col5High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col5High, Expr.products]
  have hlc : (GeneratedArithmetic.col5High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col5High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col5_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 5, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col5Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col5_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col5_sumBound carry a n (col5Qs carry minv a n q) ha hn (col5_qsBound carry minv a n q hq))

#print axioms col5_carryBound

def col6Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col6High carry a n (col6Qs carry minv a n q)).value

theorem col6_post (carry minv : UInt256) (a n q : Nat → UInt256) :
    col6Sum carry minv a n q = (col6Pre carry a n q).value + (GeneratedColumns.col6Cancel carry modulusWord maskWord minv a n q).toNat*(n 0).toNat := by
  simp only [col6Sum, GeneratedArithmetic.col6High, col6Qs, col6Pre, Expr.value]
  norm_num
  ring

theorem col6_cancels (carry minv : UInt256) (a n q : Nat → UInt256) (N : Nat)
    (hn0 : (n 0).toNat = N % 2^244)
    (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    col6Sum carry minv a n q % 2^244 = 0 := by
  rw [col6_post, col6_cancelExpr]
  exact (maskedDigitCancels (col6Pre carry a n q).low minv 244 244
    (col6Pre carry a n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue _) hn0 hinv).2.1

#print axioms col6_cancels

theorem col6_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col6High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col6High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 6) radix (hn 0 (by decide)) (hq 6 (by decide)), ⟨productBound (n 1) (q 5) radix (hn 1 (by decide)) (hq 5 (by decide)), ⟨productBound (n 2) (q 4) radix (hn 2 (by decide)) (hq 4 (by decide)), ⟨productBound (n 3) (q 3) radix (hn 3 (by decide)) (hq 3 (by decide)), ⟨productBound (n 4) (q 2) radix (hn 4 (by decide)) (hq 2 (by decide)), ⟨productBound (n 5) (q 1) radix (hn 5 (by decide)) (hq 1 (by decide)), ⟨productBound (n 6) (q 0) radix (hn 6 (by decide)) (hq 0 (by decide)), ⟨productBound (a 3) (a 3) radix (ha 3 (by decide)) (ha 3 (by decide)), ⟨True.intro, ⟨⟨productBound (a 2) (a 4) radix (ha 2 (by decide)) (ha 4 (by decide)), ⟨productBound (a 1) (a 5) radix (ha 1 (by decide)) (ha 5 (by decide)), productBound (a 6) (a 0) radix (ha 6 (by decide)) (ha 0 (by decide))⟩⟩, ⟨productBound (a 2) (a 4) radix (ha 2 (by decide)) (ha 4 (by decide)), ⟨productBound (a 1) (a 5) radix (ha 1 (by decide)) (ha 5 (by decide)), productBound (a 6) (a 0) radix (ha 6 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col6High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col6High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col6High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col6High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col6High, Expr.products]
  have hlc : (GeneratedArithmetic.col6High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col6High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col6_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 6, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col6Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col6_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col6_sumBound carry a n (col6Qs carry minv a n q) ha hn (col6_qsBound carry minv a n q hq))

#print axioms col6_carryBound

def col7Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col7High carry a n (col7Qs carry minv a n q)).value

theorem col7_post (carry minv : UInt256) (a n q : Nat → UInt256) :
    col7Sum carry minv a n q = (col7Pre carry a n q).value + (GeneratedColumns.col7Cancel carry modulusWord maskWord minv a n q).toNat*(n 0).toNat := by
  simp only [col7Sum, GeneratedArithmetic.col7High, col7Qs, col7Pre, Expr.value]
  norm_num
  ring

theorem col7_cancels (carry minv : UInt256) (a n q : Nat → UInt256) (N : Nat)
    (hn0 : (n 0).toNat = N % 2^244)
    (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    col7Sum carry minv a n q % 2^244 = 0 := by
  rw [col7_post, col7_cancelExpr]
  exact (maskedDigitCancels (col7Pre carry a n q).low minv 244 244
    (col7Pre carry a n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue _) hn0 hinv).2.1

#print axioms col7_cancels

theorem col7_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col7High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col7High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 7) radix (hn 0 (by decide)) (hq 7 (by decide)), ⟨productBound (n 1) (q 6) radix (hn 1 (by decide)) (hq 6 (by decide)), ⟨productBound (n 2) (q 5) radix (hn 2 (by decide)) (hq 5 (by decide)), ⟨productBound (n 3) (q 4) radix (hn 3 (by decide)) (hq 4 (by decide)), ⟨productBound (n 4) (q 3) radix (hn 4 (by decide)) (hq 3 (by decide)), ⟨productBound (n 5) (q 2) radix (hn 5 (by decide)) (hq 2 (by decide)), ⟨productBound (n 6) (q 1) radix (hn 6 (by decide)) (hq 1 (by decide)), ⟨productBound (n 7) (q 0) radix (hn 7 (by decide)) (hq 0 (by decide)), ⟨True.intro, ⟨⟨productBound (a 3) (a 4) radix (ha 3 (by decide)) (ha 4 (by decide)), ⟨productBound (a 2) (a 5) radix (ha 2 (by decide)) (ha 5 (by decide)), ⟨productBound (a 1) (a 6) radix (ha 1 (by decide)) (ha 6 (by decide)), productBound (a 7) (a 0) radix (ha 7 (by decide)) (ha 0 (by decide))⟩⟩⟩, ⟨productBound (a 3) (a 4) radix (ha 3 (by decide)) (ha 4 (by decide)), ⟨productBound (a 2) (a 5) radix (ha 2 (by decide)) (ha 5 (by decide)), ⟨productBound (a 1) (a 6) radix (ha 1 (by decide)) (ha 6 (by decide)), productBound (a 7) (a 0) radix (ha 7 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col7High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col7High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col7High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col7High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col7High, Expr.products]
  have hlc : (GeneratedArithmetic.col7High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col7High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col7_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 7, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col7Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col7_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col7_sumBound carry a n (col7Qs carry minv a n q) ha hn (col7_qsBound carry minv a n q hq))

#print axioms col7_carryBound

def col8Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col8High carry a n (col8Qs carry minv a n q)).value

theorem col8_post (carry minv : UInt256) (a n q : Nat → UInt256) :
    col8Sum carry minv a n q = (col8Pre carry a n q).value + (GeneratedColumns.col8Cancel carry modulusWord maskWord minv a n q).toNat*(n 0).toNat := by
  simp only [col8Sum, GeneratedArithmetic.col8High, col8Qs, col8Pre, Expr.value]
  norm_num
  ring

theorem col8_cancels (carry minv : UInt256) (a n q : Nat → UInt256) (N : Nat)
    (hn0 : (n 0).toNat = N % 2^244)
    (hinv : (N*minv.toNat+1) % 2^256 = 0) :
    col8Sum carry minv a n q % 2^96 = 0 := by
  rw [col8_post, col8_cancelExpr]
  exact (maskedDigitCancels (col8Pre carry a n q).low minv 244 96
    (col8Pre carry a n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue _) hn0 hinv).2.1

#print axioms col8_cancels

theorem col8_digitLink (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col8Digit carry modulusWord maskWord minv a n q =
      UInt256.land maskWord (GeneratedArithmetic.col8Low carry a n (col8Qs carry minv a n q)).low := by rfl

theorem col8_digit (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col8Digit carry modulusWord maskWord minv a n q).toNat = col8Sum carry minv a n q % radix := by
  rw [col8_digitLink, land_comm]
  change (((GeneratedArithmetic.col8Low carry a n (col8Qs carry minv a n q)).low) &&& UInt256.ofNat (2^244-1)).toNat = _
  rw [mask_toNat _ 244 (by decide), lowValue]
  change ((GeneratedArithmetic.col8High carry a n (col8Qs carry minv a n q)).value % 2^256) % 2^244 = _
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 244 ≤ 256))

#print axioms col8_digit

theorem col8_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col8High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col8High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 8) radix (hn 0 (by decide)) (hq 8 (by decide)), ⟨productBound (n 1) (q 7) radix (hn 1 (by decide)) (hq 7 (by decide)), ⟨productBound (n 2) (q 6) radix (hn 2 (by decide)) (hq 6 (by decide)), ⟨productBound (n 3) (q 5) radix (hn 3 (by decide)) (hq 5 (by decide)), ⟨productBound (n 4) (q 4) radix (hn 4 (by decide)) (hq 4 (by decide)), ⟨productBound (n 5) (q 3) radix (hn 5 (by decide)) (hq 3 (by decide)), ⟨productBound (n 6) (q 2) radix (hn 6 (by decide)) (hq 2 (by decide)), ⟨productBound (n 7) (q 1) radix (hn 7 (by decide)) (hq 1 (by decide)), ⟨productBound (n 8) (q 0) radix (hn 8 (by decide)) (hq 0 (by decide)), ⟨productBound (a 4) (a 4) radix (ha 4 (by decide)) (ha 4 (by decide)), ⟨True.intro, ⟨⟨productBound (a 3) (a 5) radix (ha 3 (by decide)) (ha 5 (by decide)), ⟨productBound (a 2) (a 6) radix (ha 2 (by decide)) (ha 6 (by decide)), ⟨productBound (a 1) (a 7) radix (ha 1 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 0) radix (ha 8 (by decide)) (ha 0 (by decide))⟩⟩⟩, ⟨productBound (a 3) (a 5) radix (ha 3 (by decide)) (ha 5 (by decide)), ⟨productBound (a 2) (a 6) radix (ha 2 (by decide)) (ha 6 (by decide)), ⟨productBound (a 1) (a 7) radix (ha 1 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 0) radix (ha 8 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col8High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col8High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col8High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col8High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col8High, Expr.products]
  have hlc : (GeneratedArithmetic.col8High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col8High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col8_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 8, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col8Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col8_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col8_sumBound carry a n (col8Qs carry minv a n q) ha hn (col8_qsBound carry minv a n q hq))

#print axioms col8_carryBound

def col9Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col9High carry a n (col9Qs carry minv a n q)).value

theorem col9_digitLink (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col9Digit carry modulusWord maskWord minv a n q =
      UInt256.land maskWord (GeneratedArithmetic.col9Low carry a n (col9Qs carry minv a n q)).low := by rfl

theorem col9_digit (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col9Digit carry modulusWord maskWord minv a n q).toNat = col9Sum carry minv a n q % radix := by
  rw [col9_digitLink, land_comm]
  change (((GeneratedArithmetic.col9Low carry a n (col9Qs carry minv a n q)).low) &&& UInt256.ofNat (2^244-1)).toNat = _
  rw [mask_toNat _ 244 (by decide), lowValue]
  change ((GeneratedArithmetic.col9High carry a n (col9Qs carry minv a n q)).value % 2^256) % 2^244 = _
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 244 ≤ 256))

#print axioms col9_digit

theorem col9_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col9High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col9High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 1) (q 8) radix (hn 1 (by decide)) (hq 8 (by decide)), ⟨productBound (n 2) (q 7) radix (hn 2 (by decide)) (hq 7 (by decide)), ⟨productBound (n 3) (q 6) radix (hn 3 (by decide)) (hq 6 (by decide)), ⟨productBound (n 4) (q 5) radix (hn 4 (by decide)) (hq 5 (by decide)), ⟨productBound (n 5) (q 4) radix (hn 5 (by decide)) (hq 4 (by decide)), ⟨productBound (n 6) (q 3) radix (hn 6 (by decide)) (hq 3 (by decide)), ⟨productBound (n 7) (q 2) radix (hn 7 (by decide)) (hq 2 (by decide)), ⟨productBound (n 8) (q 1) radix (hn 8 (by decide)) (hq 1 (by decide)), ⟨True.intro, ⟨⟨productBound (a 4) (a 5) radix (ha 4 (by decide)) (ha 5 (by decide)), ⟨productBound (a 3) (a 6) radix (ha 3 (by decide)) (ha 6 (by decide)), ⟨productBound (a 2) (a 7) radix (ha 2 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 1) radix (ha 8 (by decide)) (ha 1 (by decide))⟩⟩⟩, ⟨productBound (a 4) (a 5) radix (ha 4 (by decide)) (ha 5 (by decide)), ⟨productBound (a 3) (a 6) radix (ha 3 (by decide)) (ha 6 (by decide)), ⟨productBound (a 2) (a 7) radix (ha 2 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 1) radix (ha 8 (by decide)) (ha 1 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col9High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col9High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col9High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col9High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col9High, Expr.products]
  have hlc : (GeneratedArithmetic.col9High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col9High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col9_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col9Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col9_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col9_sumBound carry a n (col9Qs carry minv a n q) ha hn (col9_qsBound carry minv a n q hq))

#print axioms col9_carryBound

def col10Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col10High carry a n (col10Qs carry minv a n q)).value

theorem col10_digitLink (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col10Digit carry modulusWord maskWord minv a n q =
      UInt256.land maskWord (GeneratedArithmetic.col10Low carry a n (col10Qs carry minv a n q)).low := by rfl

theorem col10_digit (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col10Digit carry modulusWord maskWord minv a n q).toNat = col10Sum carry minv a n q % radix := by
  rw [col10_digitLink, land_comm]
  change (((GeneratedArithmetic.col10Low carry a n (col10Qs carry minv a n q)).low) &&& UInt256.ofNat (2^244-1)).toNat = _
  rw [mask_toNat _ 244 (by decide), lowValue]
  change ((GeneratedArithmetic.col10High carry a n (col10Qs carry minv a n q)).value % 2^256) % 2^244 = _
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 244 ≤ 256))

#print axioms col10_digit

theorem col10_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col10High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col10High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 2) (q 8) radix (hn 2 (by decide)) (hq 8 (by decide)), ⟨productBound (n 3) (q 7) radix (hn 3 (by decide)) (hq 7 (by decide)), ⟨productBound (n 4) (q 6) radix (hn 4 (by decide)) (hq 6 (by decide)), ⟨productBound (n 5) (q 5) radix (hn 5 (by decide)) (hq 5 (by decide)), ⟨productBound (n 6) (q 4) radix (hn 6 (by decide)) (hq 4 (by decide)), ⟨productBound (n 7) (q 3) radix (hn 7 (by decide)) (hq 3 (by decide)), ⟨productBound (n 8) (q 2) radix (hn 8 (by decide)) (hq 2 (by decide)), ⟨productBound (a 5) (a 5) radix (ha 5 (by decide)) (ha 5 (by decide)), ⟨True.intro, ⟨⟨productBound (a 4) (a 6) radix (ha 4 (by decide)) (ha 6 (by decide)), ⟨productBound (a 3) (a 7) radix (ha 3 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 2) radix (ha 8 (by decide)) (ha 2 (by decide))⟩⟩, ⟨productBound (a 4) (a 6) radix (ha 4 (by decide)) (ha 6 (by decide)), ⟨productBound (a 3) (a 7) radix (ha 3 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 2) radix (ha 8 (by decide)) (ha 2 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col10High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col10High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col10High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col10High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col10High, Expr.products]
  have hlc : (GeneratedArithmetic.col10High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col10High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col10_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col10Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col10_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col10_sumBound carry a n (col10Qs carry minv a n q) ha hn (col10_qsBound carry minv a n q hq))

#print axioms col10_carryBound

def col11Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col11High carry a n (col11Qs carry minv a n q)).value

theorem col11_digitLink (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col11Digit carry modulusWord maskWord minv a n q =
      UInt256.land maskWord (GeneratedArithmetic.col11Low carry a n (col11Qs carry minv a n q)).low := by rfl

theorem col11_digit (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col11Digit carry modulusWord maskWord minv a n q).toNat = col11Sum carry minv a n q % radix := by
  rw [col11_digitLink, land_comm]
  change (((GeneratedArithmetic.col11Low carry a n (col11Qs carry minv a n q)).low) &&& UInt256.ofNat (2^244-1)).toNat = _
  rw [mask_toNat _ 244 (by decide), lowValue]
  change ((GeneratedArithmetic.col11High carry a n (col11Qs carry minv a n q)).value % 2^256) % 2^244 = _
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 244 ≤ 256))

#print axioms col11_digit

theorem col11_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col11High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col11High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 3) (q 8) radix (hn 3 (by decide)) (hq 8 (by decide)), ⟨productBound (n 4) (q 7) radix (hn 4 (by decide)) (hq 7 (by decide)), ⟨productBound (n 5) (q 6) radix (hn 5 (by decide)) (hq 6 (by decide)), ⟨productBound (n 6) (q 5) radix (hn 6 (by decide)) (hq 5 (by decide)), ⟨productBound (n 7) (q 4) radix (hn 7 (by decide)) (hq 4 (by decide)), ⟨productBound (n 8) (q 3) radix (hn 8 (by decide)) (hq 3 (by decide)), ⟨True.intro, ⟨⟨productBound (a 5) (a 6) radix (ha 5 (by decide)) (ha 6 (by decide)), ⟨productBound (a 4) (a 7) radix (ha 4 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 3) radix (ha 8 (by decide)) (ha 3 (by decide))⟩⟩, ⟨productBound (a 5) (a 6) radix (ha 5 (by decide)) (ha 6 (by decide)), ⟨productBound (a 4) (a 7) radix (ha 4 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 3) radix (ha 8 (by decide)) (ha 3 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col11High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col11High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col11High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col11High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col11High, Expr.products]
  have hlc : (GeneratedArithmetic.col11High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col11High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col11_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col11Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col11_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col11_sumBound carry a n (col11Qs carry minv a n q) ha hn (col11_qsBound carry minv a n q hq))

#print axioms col11_carryBound

def col12Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col12High carry a n (col12Qs carry minv a n q)).value

theorem col12_digitLink (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col12Digit carry modulusWord maskWord minv a n q =
      UInt256.land maskWord (GeneratedArithmetic.col12Low carry a n (col12Qs carry minv a n q)).low := by rfl

theorem col12_digit (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col12Digit carry modulusWord maskWord minv a n q).toNat = col12Sum carry minv a n q % radix := by
  rw [col12_digitLink, land_comm]
  change (((GeneratedArithmetic.col12Low carry a n (col12Qs carry minv a n q)).low) &&& UInt256.ofNat (2^244-1)).toNat = _
  rw [mask_toNat _ 244 (by decide), lowValue]
  change ((GeneratedArithmetic.col12High carry a n (col12Qs carry minv a n q)).value % 2^256) % 2^244 = _
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 244 ≤ 256))

#print axioms col12_digit

theorem col12_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col12High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col12High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 4) (q 8) radix (hn 4 (by decide)) (hq 8 (by decide)), ⟨productBound (n 5) (q 7) radix (hn 5 (by decide)) (hq 7 (by decide)), ⟨productBound (n 6) (q 6) radix (hn 6 (by decide)) (hq 6 (by decide)), ⟨productBound (n 7) (q 5) radix (hn 7 (by decide)) (hq 5 (by decide)), ⟨productBound (n 8) (q 4) radix (hn 8 (by decide)) (hq 4 (by decide)), ⟨productBound (a 6) (a 6) radix (ha 6 (by decide)) (ha 6 (by decide)), ⟨True.intro, ⟨⟨productBound (a 5) (a 7) radix (ha 5 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 4) radix (ha 8 (by decide)) (ha 4 (by decide))⟩, ⟨productBound (a 5) (a 7) radix (ha 5 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 4) radix (ha 8 (by decide)) (ha 4 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col12High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col12High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col12High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col12High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col12High, Expr.products]
  have hlc : (GeneratedArithmetic.col12High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col12High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col12_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col12Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col12_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col12_sumBound carry a n (col12Qs carry minv a n q) ha hn (col12_qsBound carry minv a n q hq))

#print axioms col12_carryBound

def col13Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col13High carry a n (col13Qs carry minv a n q)).value

theorem col13_digitLink (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col13Digit carry modulusWord maskWord minv a n q =
      UInt256.land maskWord (GeneratedArithmetic.col13Low carry a n (col13Qs carry minv a n q)).low := by rfl

theorem col13_digit (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col13Digit carry modulusWord maskWord minv a n q).toNat = col13Sum carry minv a n q % radix := by
  rw [col13_digitLink, land_comm]
  change (((GeneratedArithmetic.col13Low carry a n (col13Qs carry minv a n q)).low) &&& UInt256.ofNat (2^244-1)).toNat = _
  rw [mask_toNat _ 244 (by decide), lowValue]
  change ((GeneratedArithmetic.col13High carry a n (col13Qs carry minv a n q)).value % 2^256) % 2^244 = _
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 244 ≤ 256))

#print axioms col13_digit

theorem col13_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col13High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col13High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 5) (q 8) radix (hn 5 (by decide)) (hq 8 (by decide)), ⟨productBound (n 6) (q 7) radix (hn 6 (by decide)) (hq 7 (by decide)), ⟨productBound (n 7) (q 6) radix (hn 7 (by decide)) (hq 6 (by decide)), ⟨productBound (n 8) (q 5) radix (hn 8 (by decide)) (hq 5 (by decide)), ⟨True.intro, ⟨⟨productBound (a 6) (a 7) radix (ha 6 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 5) radix (ha 8 (by decide)) (ha 5 (by decide))⟩, ⟨productBound (a 6) (a 7) radix (ha 6 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 5) radix (ha 8 (by decide)) (ha 5 (by decide))⟩⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col13High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col13High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col13High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col13High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col13High, Expr.products]
  have hlc : (GeneratedArithmetic.col13High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col13High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col13_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col13Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col13_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col13_sumBound carry a n (col13Qs carry minv a n q) ha hn (col13_qsBound carry minv a n q hq))

#print axioms col13_carryBound

def col14Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col14High carry a n (col14Qs carry minv a n q)).value

theorem col14_digitLink (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col14Digit carry modulusWord maskWord minv a n q =
      UInt256.land maskWord (GeneratedArithmetic.col14Low carry a n (col14Qs carry minv a n q)).low := by rfl

theorem col14_digit (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col14Digit carry modulusWord maskWord minv a n q).toNat = col14Sum carry minv a n q % radix := by
  rw [col14_digitLink, land_comm]
  change (((GeneratedArithmetic.col14Low carry a n (col14Qs carry minv a n q)).low) &&& UInt256.ofNat (2^244-1)).toNat = _
  rw [mask_toNat _ 244 (by decide), lowValue]
  change ((GeneratedArithmetic.col14High carry a n (col14Qs carry minv a n q)).value % 2^256) % 2^244 = _
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 244 ≤ 256))

#print axioms col14_digit

theorem col14_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col14High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col14High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 6) (q 8) radix (hn 6 (by decide)) (hq 8 (by decide)), ⟨productBound (n 7) (q 7) radix (hn 7 (by decide)) (hq 7 (by decide)), ⟨productBound (n 8) (q 6) radix (hn 8 (by decide)) (hq 6 (by decide)), ⟨productBound (a 7) (a 7) radix (ha 7 (by decide)) (ha 7 (by decide)), ⟨True.intro, ⟨productBound (a 8) (a 6) radix (ha 8 (by decide)) (ha 6 (by decide)), productBound (a 8) (a 6) radix (ha 8 (by decide)) (ha 6 (by decide))⟩⟩⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col14High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col14High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col14High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col14High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col14High, Expr.products]
  have hlc : (GeneratedArithmetic.col14High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col14High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col14_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col14Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col14_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col14_sumBound carry a n (col14Qs carry minv a n q) ha hn (col14_qsBound carry minv a n q hq))

#print axioms col14_carryBound

def col15Sum (carry minv : UInt256) (a n q : Nat → UInt256) : Nat := (GeneratedArithmetic.col15High carry a n (col15Qs carry minv a n q)).value

theorem col15_digitLink (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col15Digit carry modulusWord maskWord minv a n q =
      UInt256.land maskWord (GeneratedArithmetic.col15Low carry a n (col15Qs carry minv a n q)).low := by rfl

theorem col15_digit (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col15Digit carry modulusWord maskWord minv a n q).toNat = col15Sum carry minv a n q % radix := by
  rw [col15_digitLink, land_comm]
  change (((GeneratedArithmetic.col15Low carry a n (col15Qs carry minv a n q)).low) &&& UInt256.ofNat (2^244-1)).toNat = _
  rw [mask_toNat _ 244 (by decide), lowValue]
  change ((GeneratedArithmetic.col15High carry a n (col15Qs carry minv a n q)).value % 2^256) % 2^244 = _
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 244 ≤ 256))

#print axioms col15_digit

theorem col15_sumBound (carry : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    (GeneratedArithmetic.col15High carry a n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (GeneratedArithmetic.col15High carry a n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 7) (q 8) radix (hn 7 (by decide)) (hq 8 (by decide)), ⟨productBound (n 8) (q 7) radix (hn 8 (by decide)) (hq 7 (by decide)), ⟨True.intro, ⟨productBound (a 8) (a 7) radix (ha 8 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 7) radix (ha 8 (by decide)) (ha 7 (by decide))⟩⟩⟩⟩
  have hl : (GeneratedArithmetic.col15High carry a n q).literalsBounded carry.toNat := by
    simp [GeneratedArithmetic.col15High, Expr.literalsBounded]
  have hb := valueBound (GeneratedArithmetic.col15High carry a n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (GeneratedArithmetic.col15High carry a n q).products ≤ 18 := by norm_num [GeneratedArithmetic.col15High, Expr.products]
  have hlc : (GeneratedArithmetic.col15High carry a n q).literals ≤ 1 := by norm_num [GeneratedArithmetic.col15High, Expr.literals]
  have hpm := Nat.mul_le_mul_right ((radix-1)^2) hpc
  have hlm := Nat.mul_le_mul_right carry.toNat hlc
  nlinarith

theorem col15_carryBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col15Carry carry modulusWord maskWord minv a n q).toNat ≤ 18*(radix-1) := by
  rw [col15_actualCarry carry minv a n q ha hn hq hc]
  exact columnCarryBound radix 18 _ carry.toNat (Nat.two_pow_pos 244) hc
    (col15_sumBound carry a n (col15Qs carry minv a n q) ha hn (col15_qsBound carry minv a n q hq))

#print axioms col15_carryBound

theorem col16_digit (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : (a 8).toNat < 2^96) (hn : (n 8).toNat < 2^96) (hq : (q 8).toNat < 2^96)
    (hc : carry.toNat ≤ 4*((2^96 : Nat)-1)+18) :
    (GeneratedColumns.col16Digit carry modulusWord maskWord minv a n q).toNat =
      (a 8).toNat*(a 8).toNat+(q 8).toNat*(n 8).toNat+carry.toNat ∧
    (GeneratedColumns.col16Digit carry modulusWord maskWord minv a n q).toNat < radix := by
  exact (TailArithmetic.col16_ordinary (a 8) (n 8) (q 8) carry ha hn hq hc).imp_right And.left

#print axioms col16_digit

end HistoricalSearch.ColumnContracts
