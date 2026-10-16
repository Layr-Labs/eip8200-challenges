import Challenge.Modexp.Submission.Proofs.CRT.GeneratedArithmetic
import Challenge.Modexp.Submission.Proofs.CRT.CRTKernelExecution
import Challenge.Modexp.Submission.Proofs.CRT.WordCancellation
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace HistoricalSearch.ConcreteArithmetic
open EvmSemantics
open HistoricalSearch.CRTColumn HistoricalSearch.ColumnExpressions
open HistoricalSearch.GeneratedArithmetic HistoricalSearch.WordCancellation
open HistoricalSearch.CRTExecution

def maskWord : UInt256 := UInt256.ofNat ((2^244 : Nat)-1)

def col0Pre (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.product (a 0) (a 0))

def col0Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 :=
  fun j => if j = 0 then GeneratedColumns.col0Cancel carry modulusWord maskWord minv a n q
    else if j < 0 then q j else UInt256.ofNat 0

theorem col0_cancelRange (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col0Cancel carry modulusWord maskWord minv a n q).toNat < 2^244 := by
  exact leftMask_lt _ 244 (by decide)

theorem col0_cancelExpr (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col0Cancel carry modulusWord maskWord minv a n q =
      maskedDigit (col0Pre carry a n q).low minv 244 244 := by
  exact maskedDigit_commute _ minv 244 244

theorem col0_cancelNat (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col0Cancel carry modulusWord maskWord minv a n q).toNat =
      ((col0Pre carry a n q).value*minv.toNat) % 2^244 := by
  rw [col0_cancelExpr]
  exact maskedDigit_toNat _ minv 244 244 _ (by decide) (by decide) (lowValue _)

theorem col0_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 0, (q j).toNat < radix) :
    ∀ j < 9, ((col0Qs carry minv a n q) j).toNat < radix := by
  intro j hj
  by_cases he : j = 0
  · subst j
    have hh := col0_cancelRange carry minv a n q
    simpa [col0Qs, radix] using hh
  · by_cases hl : j < 0
    · simpa only [col0Qs, if_neg he, if_pos hl] using hq j hl
    · simp [col0Qs, he, hl, radix, UInt256.ofNat, UInt256.toNat]

theorem col0_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col0Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col0High carry a n (col0Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col0Low carry a n (col0Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col0_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 0, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col0Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col0High carry a n (col0Qs carry minv a n q)).value / radix := by
  rw [col0_link]
  exact GeneratedArithmetic.col0_carry carry a n (col0Qs carry minv a n q) ha hn
    (col0_qsBound carry minv a n q hq) hc

#print axioms col0_actualCarry

#print axioms col0_cancelNat

def col1Pre (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 1) (a 0)) (Expr.product (a 1) (a 0)))))

def col1Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 :=
  fun j => if j = 1 then GeneratedColumns.col1Cancel carry modulusWord maskWord minv a n q
    else if j < 1 then q j else UInt256.ofNat 0

theorem col1_cancelRange (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col1Cancel carry modulusWord maskWord minv a n q).toNat < 2^244 := by
  exact leftMask_lt _ 244 (by decide)

theorem col1_cancelExpr (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col1Cancel carry modulusWord maskWord minv a n q =
      maskedDigit (col1Pre carry a n q).low minv 244 244 := by
  exact maskedDigit_commute _ minv 244 244

theorem col1_cancelNat (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col1Cancel carry modulusWord maskWord minv a n q).toNat =
      ((col1Pre carry a n q).value*minv.toNat) % 2^244 := by
  rw [col1_cancelExpr]
  exact maskedDigit_toNat _ minv 244 244 _ (by decide) (by decide) (lowValue _)

theorem col1_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 1, (q j).toNat < radix) :
    ∀ j < 9, ((col1Qs carry minv a n q) j).toNat < radix := by
  intro j hj
  by_cases he : j = 1
  · subst j
    have hh := col1_cancelRange carry minv a n q
    simpa [col1Qs, radix] using hh
  · by_cases hl : j < 1
    · simpa only [col1Qs, if_neg he, if_pos hl] using hq j hl
    · simp [col1Qs, he, hl, radix, UInt256.ofNat, UInt256.toNat]

theorem col1_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col1Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col1High carry a n (col1Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col1Low carry a n (col1Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col1_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 1, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col1Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col1High carry a n (col1Qs carry minv a n q)).value / radix := by
  rw [col1_link]
  exact GeneratedArithmetic.col1_carry carry a n (col1Qs carry minv a n q) ha hn
    (col1_qsBound carry minv a n q hq) hc

#print axioms col1_actualCarry

#print axioms col1_cancelNat

def col2Pre (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 1)) (Expr.add (Expr.product (n 2) (q 0)) (Expr.add (Expr.product (a 1) (a 1)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 2) (a 0)) (Expr.product (a 2) (a 0)))))))

def col2Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 :=
  fun j => if j = 2 then GeneratedColumns.col2Cancel carry modulusWord maskWord minv a n q
    else if j < 2 then q j else UInt256.ofNat 0

theorem col2_cancelRange (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col2Cancel carry modulusWord maskWord minv a n q).toNat < 2^244 := by
  exact leftMask_lt _ 244 (by decide)

theorem col2_cancelExpr (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col2Cancel carry modulusWord maskWord minv a n q =
      maskedDigit (col2Pre carry a n q).low minv 244 244 := by
  exact maskedDigit_commute _ minv 244 244

theorem col2_cancelNat (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col2Cancel carry modulusWord maskWord minv a n q).toNat =
      ((col2Pre carry a n q).value*minv.toNat) % 2^244 := by
  rw [col2_cancelExpr]
  exact maskedDigit_toNat _ minv 244 244 _ (by decide) (by decide) (lowValue _)

theorem col2_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 2, (q j).toNat < radix) :
    ∀ j < 9, ((col2Qs carry minv a n q) j).toNat < radix := by
  intro j hj
  by_cases he : j = 2
  · subst j
    have hh := col2_cancelRange carry minv a n q
    simpa [col2Qs, radix] using hh
  · by_cases hl : j < 2
    · simpa only [col2Qs, if_neg he, if_pos hl] using hq j hl
    · simp [col2Qs, he, hl, radix, UInt256.ofNat, UInt256.toNat]

theorem col2_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col2Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col2High carry a n (col2Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col2Low carry a n (col2Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col2_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 2, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col2Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col2High carry a n (col2Qs carry minv a n q)).value / radix := by
  rw [col2_link]
  exact GeneratedArithmetic.col2_carry carry a n (col2Qs carry minv a n q) ha hn
    (col2_qsBound carry minv a n q hq) hc

#print axioms col2_actualCarry

#print axioms col2_cancelNat

def col3Pre (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 2)) (Expr.add (Expr.product (n 2) (q 1)) (Expr.add (Expr.product (n 3) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 1) (a 2)) (Expr.product (a 3) (a 0))) (Expr.add (Expr.product (a 1) (a 2)) (Expr.product (a 3) (a 0))))))))

def col3Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 :=
  fun j => if j = 3 then GeneratedColumns.col3Cancel carry modulusWord maskWord minv a n q
    else if j < 3 then q j else UInt256.ofNat 0

theorem col3_cancelRange (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col3Cancel carry modulusWord maskWord minv a n q).toNat < 2^244 := by
  exact leftMask_lt _ 244 (by decide)

theorem col3_cancelExpr (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col3Cancel carry modulusWord maskWord minv a n q =
      maskedDigit (col3Pre carry a n q).low minv 244 244 := by
  exact maskedDigit_commute _ minv 244 244

theorem col3_cancelNat (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col3Cancel carry modulusWord maskWord minv a n q).toNat =
      ((col3Pre carry a n q).value*minv.toNat) % 2^244 := by
  rw [col3_cancelExpr]
  exact maskedDigit_toNat _ minv 244 244 _ (by decide) (by decide) (lowValue _)

theorem col3_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 3, (q j).toNat < radix) :
    ∀ j < 9, ((col3Qs carry minv a n q) j).toNat < radix := by
  intro j hj
  by_cases he : j = 3
  · subst j
    have hh := col3_cancelRange carry minv a n q
    simpa [col3Qs, radix] using hh
  · by_cases hl : j < 3
    · simpa only [col3Qs, if_neg he, if_pos hl] using hq j hl
    · simp [col3Qs, he, hl, radix, UInt256.ofNat, UInt256.toNat]

theorem col3_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col3Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col3High carry a n (col3Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col3Low carry a n (col3Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col3_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 3, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col3Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col3High carry a n (col3Qs carry minv a n q)).value / radix := by
  rw [col3_link]
  exact GeneratedArithmetic.col3_carry carry a n (col3Qs carry minv a n q) ha hn
    (col3_qsBound carry minv a n q hq) hc

#print axioms col3_actualCarry

#print axioms col3_cancelNat

def col4Pre (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 3)) (Expr.add (Expr.product (n 2) (q 2)) (Expr.add (Expr.product (n 3) (q 1)) (Expr.add (Expr.product (n 4) (q 0)) (Expr.add (Expr.product (a 2) (a 2)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 1) (a 3)) (Expr.product (a 4) (a 0))) (Expr.add (Expr.product (a 1) (a 3)) (Expr.product (a 4) (a 0))))))))))

def col4Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 :=
  fun j => if j = 4 then GeneratedColumns.col4Cancel carry modulusWord maskWord minv a n q
    else if j < 4 then q j else UInt256.ofNat 0

theorem col4_cancelRange (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col4Cancel carry modulusWord maskWord minv a n q).toNat < 2^244 := by
  exact leftMask_lt _ 244 (by decide)

theorem col4_cancelExpr (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col4Cancel carry modulusWord maskWord minv a n q =
      maskedDigit (col4Pre carry a n q).low minv 244 244 := by
  exact maskedDigit_commute _ minv 244 244

theorem col4_cancelNat (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col4Cancel carry modulusWord maskWord minv a n q).toNat =
      ((col4Pre carry a n q).value*minv.toNat) % 2^244 := by
  rw [col4_cancelExpr]
  exact maskedDigit_toNat _ minv 244 244 _ (by decide) (by decide) (lowValue _)

theorem col4_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 4, (q j).toNat < radix) :
    ∀ j < 9, ((col4Qs carry minv a n q) j).toNat < radix := by
  intro j hj
  by_cases he : j = 4
  · subst j
    have hh := col4_cancelRange carry minv a n q
    simpa [col4Qs, radix] using hh
  · by_cases hl : j < 4
    · simpa only [col4Qs, if_neg he, if_pos hl] using hq j hl
    · simp [col4Qs, he, hl, radix, UInt256.ofNat, UInt256.toNat]

theorem col4_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col4Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col4High carry a n (col4Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col4Low carry a n (col4Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col4_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 4, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col4Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col4High carry a n (col4Qs carry minv a n q)).value / radix := by
  rw [col4_link]
  exact GeneratedArithmetic.col4_carry carry a n (col4Qs carry minv a n q) ha hn
    (col4_qsBound carry minv a n q hq) hc

#print axioms col4_actualCarry

#print axioms col4_cancelNat

def col5Pre (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 4)) (Expr.add (Expr.product (n 2) (q 3)) (Expr.add (Expr.product (n 3) (q 2)) (Expr.add (Expr.product (n 4) (q 1)) (Expr.add (Expr.product (n 5) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 2) (a 3)) (Expr.add (Expr.product (a 1) (a 4)) (Expr.product (a 5) (a 0)))) (Expr.add (Expr.product (a 2) (a 3)) (Expr.add (Expr.product (a 1) (a 4)) (Expr.product (a 5) (a 0)))))))))))

def col5Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 :=
  fun j => if j = 5 then GeneratedColumns.col5Cancel carry modulusWord maskWord minv a n q
    else if j < 5 then q j else UInt256.ofNat 0

theorem col5_cancelRange (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col5Cancel carry modulusWord maskWord minv a n q).toNat < 2^244 := by
  exact leftMask_lt _ 244 (by decide)

theorem col5_cancelExpr (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col5Cancel carry modulusWord maskWord minv a n q =
      maskedDigit (col5Pre carry a n q).low minv 244 244 := by
  exact maskedDigit_commute _ minv 244 244

theorem col5_cancelNat (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col5Cancel carry modulusWord maskWord minv a n q).toNat =
      ((col5Pre carry a n q).value*minv.toNat) % 2^244 := by
  rw [col5_cancelExpr]
  exact maskedDigit_toNat _ minv 244 244 _ (by decide) (by decide) (lowValue _)

theorem col5_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 5, (q j).toNat < radix) :
    ∀ j < 9, ((col5Qs carry minv a n q) j).toNat < radix := by
  intro j hj
  by_cases he : j = 5
  · subst j
    have hh := col5_cancelRange carry minv a n q
    simpa [col5Qs, radix] using hh
  · by_cases hl : j < 5
    · simpa only [col5Qs, if_neg he, if_pos hl] using hq j hl
    · simp [col5Qs, he, hl, radix, UInt256.ofNat, UInt256.toNat]

theorem col5_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col5Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col5High carry a n (col5Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col5Low carry a n (col5Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col5_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 5, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col5Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col5High carry a n (col5Qs carry minv a n q)).value / radix := by
  rw [col5_link]
  exact GeneratedArithmetic.col5_carry carry a n (col5Qs carry minv a n q) ha hn
    (col5_qsBound carry minv a n q hq) hc

#print axioms col5_actualCarry

#print axioms col5_cancelNat

def col6Pre (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 5)) (Expr.add (Expr.product (n 2) (q 4)) (Expr.add (Expr.product (n 3) (q 3)) (Expr.add (Expr.product (n 4) (q 2)) (Expr.add (Expr.product (n 5) (q 1)) (Expr.add (Expr.product (n 6) (q 0)) (Expr.add (Expr.product (a 3) (a 3)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 2) (a 4)) (Expr.add (Expr.product (a 1) (a 5)) (Expr.product (a 6) (a 0)))) (Expr.add (Expr.product (a 2) (a 4)) (Expr.add (Expr.product (a 1) (a 5)) (Expr.product (a 6) (a 0)))))))))))))

def col6Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 :=
  fun j => if j = 6 then GeneratedColumns.col6Cancel carry modulusWord maskWord minv a n q
    else if j < 6 then q j else UInt256.ofNat 0

theorem col6_cancelRange (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col6Cancel carry modulusWord maskWord minv a n q).toNat < 2^244 := by
  exact leftMask_lt _ 244 (by decide)

theorem col6_cancelExpr (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col6Cancel carry modulusWord maskWord minv a n q =
      maskedDigit (col6Pre carry a n q).low minv 244 244 := by
  exact maskedDigit_commute _ minv 244 244

theorem col6_cancelNat (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col6Cancel carry modulusWord maskWord minv a n q).toNat =
      ((col6Pre carry a n q).value*minv.toNat) % 2^244 := by
  rw [col6_cancelExpr]
  exact maskedDigit_toNat _ minv 244 244 _ (by decide) (by decide) (lowValue _)

theorem col6_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 6, (q j).toNat < radix) :
    ∀ j < 9, ((col6Qs carry minv a n q) j).toNat < radix := by
  intro j hj
  by_cases he : j = 6
  · subst j
    have hh := col6_cancelRange carry minv a n q
    simpa [col6Qs, radix] using hh
  · by_cases hl : j < 6
    · simpa only [col6Qs, if_neg he, if_pos hl] using hq j hl
    · simp [col6Qs, he, hl, radix, UInt256.ofNat, UInt256.toNat]

theorem col6_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col6Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col6High carry a n (col6Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col6Low carry a n (col6Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col6_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 6, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col6Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col6High carry a n (col6Qs carry minv a n q)).value / radix := by
  rw [col6_link]
  exact GeneratedArithmetic.col6_carry carry a n (col6Qs carry minv a n q) ha hn
    (col6_qsBound carry minv a n q hq) hc

#print axioms col6_actualCarry

#print axioms col6_cancelNat

def col7Pre (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 6)) (Expr.add (Expr.product (n 2) (q 5)) (Expr.add (Expr.product (n 3) (q 4)) (Expr.add (Expr.product (n 4) (q 3)) (Expr.add (Expr.product (n 5) (q 2)) (Expr.add (Expr.product (n 6) (q 1)) (Expr.add (Expr.product (n 7) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 3) (a 4)) (Expr.add (Expr.product (a 2) (a 5)) (Expr.add (Expr.product (a 1) (a 6)) (Expr.product (a 7) (a 0))))) (Expr.add (Expr.product (a 3) (a 4)) (Expr.add (Expr.product (a 2) (a 5)) (Expr.add (Expr.product (a 1) (a 6)) (Expr.product (a 7) (a 0))))))))))))))

def col7Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 :=
  fun j => if j = 7 then GeneratedColumns.col7Cancel carry modulusWord maskWord minv a n q
    else if j < 7 then q j else UInt256.ofNat 0

theorem col7_cancelRange (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col7Cancel carry modulusWord maskWord minv a n q).toNat < 2^244 := by
  exact leftMask_lt _ 244 (by decide)

theorem col7_cancelExpr (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col7Cancel carry modulusWord maskWord minv a n q =
      maskedDigit (col7Pre carry a n q).low minv 244 244 := by
  exact maskedDigit_commute _ minv 244 244

theorem col7_cancelNat (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col7Cancel carry modulusWord maskWord minv a n q).toNat =
      ((col7Pre carry a n q).value*minv.toNat) % 2^244 := by
  rw [col7_cancelExpr]
  exact maskedDigit_toNat _ minv 244 244 _ (by decide) (by decide) (lowValue _)

theorem col7_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 7, (q j).toNat < radix) :
    ∀ j < 9, ((col7Qs carry minv a n q) j).toNat < radix := by
  intro j hj
  by_cases he : j = 7
  · subst j
    have hh := col7_cancelRange carry minv a n q
    simpa [col7Qs, radix] using hh
  · by_cases hl : j < 7
    · simpa only [col7Qs, if_neg he, if_pos hl] using hq j hl
    · simp [col7Qs, he, hl, radix, UInt256.ofNat, UInt256.toNat]

theorem col7_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col7Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col7High carry a n (col7Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col7Low carry a n (col7Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col7_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 7, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col7Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col7High carry a n (col7Qs carry minv a n q)).value / radix := by
  rw [col7_link]
  exact GeneratedArithmetic.col7_carry carry a n (col7Qs carry minv a n q) ha hn
    (col7_qsBound carry minv a n q hq) hc

#print axioms col7_actualCarry

#print axioms col7_cancelNat

def col8Pre (carry : UInt256) (a n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 7)) (Expr.add (Expr.product (n 2) (q 6)) (Expr.add (Expr.product (n 3) (q 5)) (Expr.add (Expr.product (n 4) (q 4)) (Expr.add (Expr.product (n 5) (q 3)) (Expr.add (Expr.product (n 6) (q 2)) (Expr.add (Expr.product (n 7) (q 1)) (Expr.add (Expr.product (n 8) (q 0)) (Expr.add (Expr.product (a 4) (a 4)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 3) (a 5)) (Expr.add (Expr.product (a 2) (a 6)) (Expr.add (Expr.product (a 1) (a 7)) (Expr.product (a 8) (a 0))))) (Expr.add (Expr.product (a 3) (a 5)) (Expr.add (Expr.product (a 2) (a 6)) (Expr.add (Expr.product (a 1) (a 7)) (Expr.product (a 8) (a 0))))))))))))))))

def col8Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 :=
  fun j => if j = 8 then GeneratedColumns.col8Cancel carry modulusWord maskWord minv a n q
    else if j < 8 then q j else UInt256.ofNat 0

theorem col8_cancelRange (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col8Cancel carry modulusWord maskWord minv a n q).toNat < 2^96 := by
  exact leftMask_lt _ 96 (by decide)

theorem col8_cancelExpr (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col8Cancel carry modulusWord maskWord minv a n q =
      maskedDigit (col8Pre carry a n q).low minv 244 96 := by
  exact maskedDigit_commute _ minv 244 96

theorem col8_cancelNat (carry minv : UInt256) (a n q : Nat → UInt256) :
    (GeneratedColumns.col8Cancel carry modulusWord maskWord minv a n q).toNat =
      ((col8Pre carry a n q).value*minv.toNat) % 2^96 := by
  rw [col8_cancelExpr]
  exact maskedDigit_toNat _ minv 244 96 _ (by decide) (by decide) (lowValue _)

theorem col8_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 8, (q j).toNat < radix) :
    ∀ j < 9, ((col8Qs carry minv a n q) j).toNat < radix := by
  intro j hj
  by_cases he : j = 8
  · subst j
    have hh := col8_cancelRange carry minv a n q
    simpa [col8Qs, radix] using hh.trans (by norm_num [radix] : (2^96 : Nat) < radix)
  · by_cases hl : j < 8
    · simpa only [col8Qs, if_neg he, if_pos hl] using hq j hl
    · simp [col8Qs, he, hl, radix, UInt256.ofNat, UInt256.toNat]

theorem col8_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col8Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col8High carry a n (col8Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col8Low carry a n (col8Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col8_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 8, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col8Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col8High carry a n (col8Qs carry minv a n q)).value / radix := by
  rw [col8_link]
  exact GeneratedArithmetic.col8_carry carry a n (col8Qs carry minv a n q) ha hn
    (col8_qsBound carry minv a n q hq) hc

#print axioms col8_actualCarry

#print axioms col8_cancelNat

def col9Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 := q

theorem col9_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    ∀ j < 9, ((col9Qs carry minv a n q) j).toNat < radix := hq

theorem col9_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col9Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col9High carry a n (col9Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col9Low carry a n (col9Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col9_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col9Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col9High carry a n (col9Qs carry minv a n q)).value / radix := by
  rw [col9_link]
  exact GeneratedArithmetic.col9_carry carry a n (col9Qs carry minv a n q) ha hn
    (col9_qsBound carry minv a n q hq) hc

#print axioms col9_actualCarry

def col10Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 := q

theorem col10_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    ∀ j < 9, ((col10Qs carry minv a n q) j).toNat < radix := hq

theorem col10_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col10Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col10High carry a n (col10Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col10Low carry a n (col10Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col10_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col10Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col10High carry a n (col10Qs carry minv a n q)).value / radix := by
  rw [col10_link]
  exact GeneratedArithmetic.col10_carry carry a n (col10Qs carry minv a n q) ha hn
    (col10_qsBound carry minv a n q hq) hc

#print axioms col10_actualCarry

def col11Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 := q

theorem col11_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    ∀ j < 9, ((col11Qs carry minv a n q) j).toNat < radix := hq

theorem col11_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col11Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col11High carry a n (col11Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col11Low carry a n (col11Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col11_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col11Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col11High carry a n (col11Qs carry minv a n q)).value / radix := by
  rw [col11_link]
  exact GeneratedArithmetic.col11_carry carry a n (col11Qs carry minv a n q) ha hn
    (col11_qsBound carry minv a n q hq) hc

#print axioms col11_actualCarry

def col12Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 := q

theorem col12_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    ∀ j < 9, ((col12Qs carry minv a n q) j).toNat < radix := hq

theorem col12_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col12Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col12High carry a n (col12Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col12Low carry a n (col12Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col12_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col12Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col12High carry a n (col12Qs carry minv a n q)).value / radix := by
  rw [col12_link]
  exact GeneratedArithmetic.col12_carry carry a n (col12Qs carry minv a n q) ha hn
    (col12_qsBound carry minv a n q hq) hc

#print axioms col12_actualCarry

def col13Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 := q

theorem col13_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    ∀ j < 9, ((col13Qs carry minv a n q) j).toNat < radix := hq

theorem col13_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col13Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col13High carry a n (col13Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col13Low carry a n (col13Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col13_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col13Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col13High carry a n (col13Qs carry minv a n q)).value / radix := by
  rw [col13_link]
  exact GeneratedArithmetic.col13_carry carry a n (col13Qs carry minv a n q) ha hn
    (col13_qsBound carry minv a n q hq) hc

#print axioms col13_actualCarry

def col14Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 := q

theorem col14_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    ∀ j < 9, ((col14Qs carry minv a n q) j).toNat < radix := hq

theorem col14_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col14Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col14High carry a n (col14Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col14Low carry a n (col14Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col14_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col14Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col14High carry a n (col14Qs carry minv a n q)).value / radix := by
  rw [col14_link]
  exact GeneratedArithmetic.col14_carry carry a n (col14Qs carry minv a n q) ha hn
    (col14_qsBound carry minv a n q hq) hc

#print axioms col14_actualCarry

def col15Qs (carry minv : UInt256) (a n q : Nat → UInt256) : Nat → UInt256 := q

theorem col15_qsBound (carry minv : UInt256) (a n q : Nat → UInt256)
    (hq : ∀ j < 9, (q j).toNat < radix) :
    ∀ j < 9, ((col15Qs carry minv a n q) j).toNat < radix := hq

theorem col15_link (carry minv : UInt256) (a n q : Nat → UInt256) :
    GeneratedColumns.col15Carry carry modulusWord maskWord minv a n q =
      carryWord ((GeneratedArithmetic.col15High carry a n (col15Qs carry minv a n q)).high modulusWord)
        (GeneratedArithmetic.col15Low carry a n (col15Qs carry minv a n q)).low modulusWord
        (UInt256.ofNat 244) (UInt256.ofNat 12) := by rfl

theorem col15_actualCarry (carry minv : UInt256) (a n q : Nat → UInt256)
    (ha : ∀ j < 9, (a j).toNat < radix)
    (hn : ∀ j < 9, (n j).toNat < radix)
    (hq : ∀ j < 9, (q j).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (GeneratedColumns.col15Carry carry modulusWord maskWord minv a n q).toNat =
      (GeneratedArithmetic.col15High carry a n (col15Qs carry minv a n q)).value / radix := by
  rw [col15_link]
  exact GeneratedArithmetic.col15_carry carry a n (col15Qs carry minv a n q) ha hn
    (col15_qsBound carry minv a n q hq) hc

#print axioms col15_actualCarry

end HistoricalSearch.ConcreteArithmetic
