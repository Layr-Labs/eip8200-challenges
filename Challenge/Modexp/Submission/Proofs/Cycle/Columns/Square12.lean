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

def square12Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 4)) (Expr.add (Expr.product (n 5) (q 7)) (Expr.add (Expr.product (q 6) (n 6)) (Expr.add (Expr.product (n 7) (q 5)) (Expr.add (Expr.product (n 8) (q 4)) (Expr.add (Expr.product (a 6) (a 6)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 5) (a 7)) (Expr.product (a 8) (a 4))) (Expr.add (Expr.product (a 5) (a 7)) (Expr.product (a 8) (a 4)))))))))))

def square12High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 4)) (Expr.add (Expr.product (n 5) (q 7)) (Expr.add (Expr.product (q 6) (n 6)) (Expr.add (Expr.product (n 7) (q 5)) (Expr.add (Expr.product (n 8) (q 4)) (Expr.add (Expr.product (a 6) (a 6)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 5) (a 7)) (Expr.product (a 8) (a 4))) (Expr.add (Expr.product (a 5) (a 7)) (Expr.product (a 8) (a 4)))))))))))

def square12Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := ((UInt256.shiftRight (((q 8) * (n 4)) + (((n 5) * (q 7)) + (((q 6) * (n 6)) + (((n 7) * (q 5)) + (((n 8) * (q 4)) + (((a 6) * (a 6)) + (carry + ((((a 5) * (a 7)) + ((a 8) * (a 4))) + (((a 5) * (a 7)) + ((a 8) * (a 4))))))))))) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod ((UInt256.mulMod (q 8) (n 4) P) + ((UInt256.mulMod (n 5) (q 7) P) + ((UInt256.mulMod (q 6) (n 6) P) + ((UInt256.mulMod (n 7) (q 5) P) + ((UInt256.mulMod (n 8) (q 4) P) + ((UInt256.mulMod (a 6) (a 6) P) + (carry + (((UInt256.mulMod (a 5) (a 7) P) + (UInt256.mulMod (a 8) (a 4) P)) + ((UInt256.mulMod (a 5) (a 7) P) + (UInt256.mulMod (a 8) (a 4) P)))))))))) (UInt256.lnot (((q 8) * (n 4)) + (((n 5) * (q 7)) + (((q 6) * (n 6)) + (((n 7) * (q 5)) + (((n 8) * (q 4)) + (((a 6) * (a 6)) + (carry + ((((a 5) * (a 7)) + ((a 8) * (a 4))) + (((a 5) * (a 7)) + ((a 8) * (a 4)))))))))))) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

theorem square12_sameValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square12High carry inv a b n q).value = (square12Low carry inv a b n q).value := by
  simp only [square12Low, square12High, Expr.value] <;> ring
def square12Digit (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((q 8) * (n 4)) + (((n 5) * (q 7)) + (((q 6) * (n 6)) + (((n 7) * (q 5)) + (((n 8) * (q 4)) + (((a 6) * (a 6)) + (carry + ((((a 5) * (a 7)) + ((a 8) * (a 4))) + (((a 5) * (a 7)) + ((a 8) * (a 4))))))))))))
def square12DigitLow (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 4)) (Expr.add (Expr.product (n 5) (q 7)) (Expr.add (Expr.product (q 6) (n 6)) (Expr.add (Expr.product (n 7) (q 5)) (Expr.add (Expr.product (n 8) (q 4)) (Expr.add (Expr.product (a 6) (a 6)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 5) (a 7)) (Expr.product (a 8) (a 4))) (Expr.add (Expr.product (a 5) (a 7)) (Expr.product (a 8) (a 4)))))))))))
theorem square12_digitValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square12DigitLow carry inv a b n q).value = (square12High carry inv a b n q).value := by
  simp only [square12DigitLow, square12High, Expr.value] <;> ring
theorem square12_digit (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square12Digit carry inv a b n q).toNat = (square12High carry inv a b n q).value % radix := by
  rw [← square12_digitValue]
  unfold square12Digit
  exact digitValue (square12DigitLow carry inv a b n q)

theorem square12_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square12High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (square12High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (q 8) (n 4) radix (hq 8 (by decide)) (hn 4 (by decide)), ⟨productBound (n 5) (q 7) radix (hn 5 (by decide)) (hq 7 (by decide)), ⟨productBound (q 6) (n 6) radix (hq 6 (by decide)) (hn 6 (by decide)), ⟨productBound (n 7) (q 5) radix (hn 7 (by decide)) (hq 5 (by decide)), ⟨productBound (n 8) (q 4) radix (hn 8 (by decide)) (hq 4 (by decide)), ⟨productBound (a 6) (a 6) radix (ha 6 (by decide)) (ha 6 (by decide)), ⟨True.intro, ⟨⟨productBound (a 5) (a 7) radix (ha 5 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 4) radix (ha 8 (by decide)) (ha 4 (by decide))⟩, ⟨productBound (a 5) (a 7) radix (ha 5 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 4) radix (ha 8 (by decide)) (ha 4 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (square12High carry inv a b n q).literalsBounded carry.toNat := by
    simp [square12High, Expr.literalsBounded]
  have hv := valueBound (square12High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (square12High carry inv a b n q).products ≤ 18 := by norm_num [square12High, Expr.products]
  have hlc : (square12High carry inv a b n q).literals ≤ 1 := by norm_num [square12High, Expr.literals]
  calc
    _ ≤ (square12High carry inv a b n q).products*((radix-1)^2) + (square12High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem square12_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((square12High carry inv a b n q).high P).toNat % residueModulus = (square12High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (square12High carry inv a b n q)
    (by norm_num [square12High, Expr.count])
    (by simp [square12High, Expr.literalsBounded, hcp])).2

theorem square12_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square12Carry carry inv a b n q).toNat = (square12High carry inv a b n q).value / radix := by
  have hs := square12_sameValue carry inv a b n q
  have hh := square12_residue carry inv a b n q hc
  have hl : (square12Low carry inv a b n q).low.toNat = (square12High carry inv a b n q).value % wordRadix := by
    rw [hs]; exact lowValue _
  have hr := rounded_contract ((square12High carry inv a b n q).high P) (square12Low carry inv a b n q).low
    (square12High carry inv a b n q).value carry.toNat hc (square12_bound carry inv a b n q ha hb hn hq hc) hl hh
  exact hr

theorem square12_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square12High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 12 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 12 := by
  simp only [square12High, Expr.value, CycleSubmission.Convolution.column12] <;> ring
end CycleSubmission.Columns
