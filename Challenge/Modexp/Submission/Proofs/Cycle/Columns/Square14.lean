import Challenge.Modexp.Submission.Proofs.Cycle.DirectRecovery
import Challenge.Modexp.Submission.Proofs.Cycle.WordArithmetic
import Challenge.Modexp.Submission.Proofs.Cycle.Convolution
import Challenge.Modexp.Submission.Proofs.CRT.CRTMaskElision
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
namespace CycleSubmission.Columns
open EvmSemantics Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.ColumnExpressions
open HistoricalSearch.WordCancellation HistoricalSearch.ProductAccumulate
open HistoricalSearch.MixedMontgomery
open CycleSubmission.WordArithmetic
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def square14Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 6)) (Expr.add (Expr.product (n 7) (q 7)) (Expr.add (Expr.product (n 8) (q 6)) (Expr.add (Expr.product (a 7) (a 7)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 8) (a 6)) (Expr.product (a 8) (a 6))))))))

def square14High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 6) (q 8)) (Expr.add (Expr.product (n 7) (q 7)) (Expr.add (Expr.product (n 8) (q 6)) (Expr.add (Expr.product (a 7) (a 7)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 8) (a 6)) (Expr.product (a 8) (a 6))))))))

def square14Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (n 6) (q 8) P) + ((UInt256.mulMod (n 7) (q 7) P) + ((UInt256.mulMod (n 8) (q 6) P) + ((UInt256.mulMod (a 7) (a 7) P) + (carry + ((UInt256.mulMod (a 8) (a 6) P) + (UInt256.mulMod (a 8) (a 6) P))))))) (((q 8) * (n 6)) + (((n 7) * (q 7)) + (((n 8) * (q 6)) + (((a 7) * (a 7)) + (carry + (((a 8) * (a 6)) + ((a 8) * (a 6)))))))))

theorem square14_sameValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square14High carry inv a b n q).value = (square14Low carry inv a b n q).value := by
  simp only [square14Low, square14High, Expr.value] <;> ring
def square14Digit (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((q 8) * (n 6)) + (((n 7) * (q 7)) + (((n 8) * (q 6)) + (((a 7) * (a 7)) + (carry + (((a 8) * (a 6)) + ((a 8) * (a 6)))))))))
def square14DigitLow (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 6)) (Expr.add (Expr.product (n 7) (q 7)) (Expr.add (Expr.product (n 8) (q 6)) (Expr.add (Expr.product (a 7) (a 7)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 8) (a 6)) (Expr.product (a 8) (a 6))))))))
theorem square14_digitValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square14DigitLow carry inv a b n q).value = (square14High carry inv a b n q).value := by
  simp only [square14DigitLow, square14High, Expr.value] <;> ring
theorem square14_digit (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square14Digit carry inv a b n q).toNat = (square14High carry inv a b n q).value % radix := by
  rw [← square14_digitValue]
  unfold square14Digit
  exact digitValue (square14DigitLow carry inv a b n q)

theorem square14_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square14High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (square14High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 6) (q 8) radix (hn 6 (by decide)) (hq 8 (by decide)), ⟨productBound (n 7) (q 7) radix (hn 7 (by decide)) (hq 7 (by decide)), ⟨productBound (n 8) (q 6) radix (hn 8 (by decide)) (hq 6 (by decide)), ⟨productBound (a 7) (a 7) radix (ha 7 (by decide)) (ha 7 (by decide)), ⟨True.intro, ⟨productBound (a 8) (a 6) radix (ha 8 (by decide)) (ha 6 (by decide)), productBound (a 8) (a 6) radix (ha 8 (by decide)) (ha 6 (by decide))⟩⟩⟩⟩⟩⟩
  have hl : (square14High carry inv a b n q).literalsBounded carry.toNat := by
    simp [square14High, Expr.literalsBounded]
  have hv := valueBound (square14High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (square14High carry inv a b n q).products ≤ 18 := by norm_num [square14High, Expr.products]
  have hlc : (square14High carry inv a b n q).literals ≤ 1 := by norm_num [square14High, Expr.literals]
  calc
    _ ≤ (square14High carry inv a b n q).products*((radix-1)^2) + (square14High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem square14_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((square14High carry inv a b n q).high P).toNat % residueModulus = (square14High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (square14High carry inv a b n q)
    (by norm_num [square14High, Expr.count])
    (by simp [square14High, Expr.literalsBounded, hcp])).2

theorem square14_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square14Carry carry inv a b n q).toNat = (square14High carry inv a b n q).value / radix := by
  have hcp : carry.toNat ≤ HistoricalSearch.CRTColumn.residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact CycleSubmission.DirectRecovery.expression_contract
    (square14High carry inv a b n q) (square14Low carry inv a b n q) carry.toNat
    (by norm_num [square14High, Expr.count])
    (by simp [square14High, Expr.literalsBounded, hcp])
    (square14_sameValue carry inv a b n q) hc
    (square14_bound carry inv a b n q ha hb hn hq hc)

theorem square14_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square14High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 14 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 14 := by
  simp only [square14High, Expr.value, CycleSubmission.Convolution.column14] <;> ring
end CycleSubmission.Columns
