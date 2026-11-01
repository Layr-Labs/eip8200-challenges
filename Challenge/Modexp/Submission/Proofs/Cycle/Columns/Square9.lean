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

def square9Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 1)) (Expr.add (Expr.product (q 7) (n 2)) (Expr.add (Expr.product (q 6) (n 3)) (Expr.add (Expr.product (q 5) (n 4)) (Expr.add (Expr.product (q 4) (n 5)) (Expr.add (Expr.product (q 3) (n 6)) (Expr.add (Expr.product (n 7) (q 2)) (Expr.add (Expr.product (n 8) (q 1)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 4) (a 5)) (Expr.add (Expr.product (a 3) (a 6)) (Expr.add (Expr.product (a 2) (a 7)) (Expr.product (a 8) (a 1))))) (Expr.add (Expr.product (a 4) (a 5)) (Expr.add (Expr.product (a 3) (a 6)) (Expr.add (Expr.product (a 2) (a 7)) (Expr.product (a 8) (a 1)))))))))))))))

def square9High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 1)) (Expr.add (Expr.product (q 7) (n 2)) (Expr.add (Expr.product (q 6) (n 3)) (Expr.add (Expr.product (q 5) (n 4)) (Expr.add (Expr.product (q 4) (n 5)) (Expr.add (Expr.product (q 3) (n 6)) (Expr.add (Expr.product (n 7) (q 2)) (Expr.add (Expr.product (n 8) (q 1)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 4) (a 5)) (Expr.add (Expr.product (a 3) (a 6)) (Expr.add (Expr.product (a 2) (a 7)) (Expr.product (a 8) (a 1))))) (Expr.add (Expr.product (a 4) (a 5)) (Expr.add (Expr.product (a 3) (a 6)) (Expr.add (Expr.product (a 2) (a 7)) (Expr.product (a 8) (a 1)))))))))))))))

def square9Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (q 8) (n 1) P) + ((UInt256.mulMod (q 7) (n 2) P) + ((UInt256.mulMod (q 6) (n 3) P) + ((UInt256.mulMod (q 5) (n 4) P) + ((UInt256.mulMod (q 4) (n 5) P) + ((UInt256.mulMod (q 3) (n 6) P) + ((UInt256.mulMod (n 7) (q 2) P) + ((UInt256.mulMod (n 8) (q 1) P) + (carry + (((UInt256.mulMod (a 4) (a 5) P) + ((UInt256.mulMod (a 3) (a 6) P) + ((UInt256.mulMod (a 2) (a 7) P) + (UInt256.mulMod (a 8) (a 1) P)))) + ((UInt256.mulMod (a 4) (a 5) P) + ((UInt256.mulMod (a 3) (a 6) P) + ((UInt256.mulMod (a 2) (a 7) P) + (UInt256.mulMod (a 8) (a 1) P)))))))))))))) (((q 8) * (n 1)) + (((q 7) * (n 2)) + (((q 6) * (n 3)) + (((q 5) * (n 4)) + (((q 4) * (n 5)) + (((q 3) * (n 6)) + (((n 7) * (q 2)) + (((n 8) * (q 1)) + (carry + ((((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1))))) + (((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1))))))))))))))))

theorem square9_sameValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square9High carry inv a b n q).value = (square9Low carry inv a b n q).value := by
  simp only [square9Low, square9High, Expr.value] <;> ring
def square9Digit (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((q 8) * (n 1)) + (((q 7) * (n 2)) + (((q 6) * (n 3)) + (((q 5) * (n 4)) + (((q 4) * (n 5)) + (((q 3) * (n 6)) + (((n 7) * (q 2)) + (((n 8) * (q 1)) + (carry + ((((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1))))) + (((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1))))))))))))))))
def square9DigitLow (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 1)) (Expr.add (Expr.product (q 7) (n 2)) (Expr.add (Expr.product (q 6) (n 3)) (Expr.add (Expr.product (q 5) (n 4)) (Expr.add (Expr.product (q 4) (n 5)) (Expr.add (Expr.product (q 3) (n 6)) (Expr.add (Expr.product (n 7) (q 2)) (Expr.add (Expr.product (n 8) (q 1)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 4) (a 5)) (Expr.add (Expr.product (a 3) (a 6)) (Expr.add (Expr.product (a 2) (a 7)) (Expr.product (a 8) (a 1))))) (Expr.add (Expr.product (a 4) (a 5)) (Expr.add (Expr.product (a 3) (a 6)) (Expr.add (Expr.product (a 2) (a 7)) (Expr.product (a 8) (a 1)))))))))))))))
theorem square9_digitValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square9DigitLow carry inv a b n q).value = (square9High carry inv a b n q).value := by
  simp only [square9DigitLow, square9High, Expr.value] <;> ring
theorem square9_digit (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square9Digit carry inv a b n q).toNat = (square9High carry inv a b n q).value % radix := by
  rw [← square9_digitValue]
  unfold square9Digit
  exact digitValue (square9DigitLow carry inv a b n q)

theorem square9_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square9High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (square9High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (q 8) (n 1) radix (hq 8 (by decide)) (hn 1 (by decide)), ⟨productBound (q 7) (n 2) radix (hq 7 (by decide)) (hn 2 (by decide)), ⟨productBound (q 6) (n 3) radix (hq 6 (by decide)) (hn 3 (by decide)), ⟨productBound (q 5) (n 4) radix (hq 5 (by decide)) (hn 4 (by decide)), ⟨productBound (q 4) (n 5) radix (hq 4 (by decide)) (hn 5 (by decide)), ⟨productBound (q 3) (n 6) radix (hq 3 (by decide)) (hn 6 (by decide)), ⟨productBound (n 7) (q 2) radix (hn 7 (by decide)) (hq 2 (by decide)), ⟨productBound (n 8) (q 1) radix (hn 8 (by decide)) (hq 1 (by decide)), ⟨True.intro, ⟨⟨productBound (a 4) (a 5) radix (ha 4 (by decide)) (ha 5 (by decide)), ⟨productBound (a 3) (a 6) radix (ha 3 (by decide)) (ha 6 (by decide)), ⟨productBound (a 2) (a 7) radix (ha 2 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 1) radix (ha 8 (by decide)) (ha 1 (by decide))⟩⟩⟩, ⟨productBound (a 4) (a 5) radix (ha 4 (by decide)) (ha 5 (by decide)), ⟨productBound (a 3) (a 6) radix (ha 3 (by decide)) (ha 6 (by decide)), ⟨productBound (a 2) (a 7) radix (ha 2 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 1) radix (ha 8 (by decide)) (ha 1 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (square9High carry inv a b n q).literalsBounded carry.toNat := by
    simp [square9High, Expr.literalsBounded]
  have hv := valueBound (square9High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (square9High carry inv a b n q).products ≤ 18 := by norm_num [square9High, Expr.products]
  have hlc : (square9High carry inv a b n q).literals ≤ 1 := by norm_num [square9High, Expr.literals]
  calc
    _ ≤ (square9High carry inv a b n q).products*((radix-1)^2) + (square9High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem square9_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((square9High carry inv a b n q).high P).toNat % residueModulus = (square9High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (square9High carry inv a b n q)
    (by norm_num [square9High, Expr.count])
    (by simp [square9High, Expr.literalsBounded, hcp])).2

theorem square9_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square9Carry carry inv a b n q).toNat = (square9High carry inv a b n q).value / radix := by
  have hcp : carry.toNat ≤ HistoricalSearch.CRTColumn.residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact CycleSubmission.DirectRecovery.expression_contract
    (square9High carry inv a b n q) (square9Low carry inv a b n q) carry.toNat
    (by norm_num [square9High, Expr.count])
    (by simp [square9High, Expr.literalsBounded, hcp])
    (square9_sameValue carry inv a b n q) hc
    (square9_bound carry inv a b n q ha hb hn hq hc)

theorem square9_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square9High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 9 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 9 := by
  simp only [square9High, Expr.value, CycleSubmission.Convolution.column9] <;> ring
end CycleSubmission.Columns
