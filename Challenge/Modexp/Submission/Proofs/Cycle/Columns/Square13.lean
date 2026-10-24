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

def square13Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 5)) (Expr.add (Expr.product (n 6) (q 7)) (Expr.add (Expr.product (n 7) (q 6)) (Expr.add (Expr.product (n 8) (q 5)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 6) (a 7)) (Expr.product (a 8) (a 5))) (Expr.add (Expr.product (a 6) (a 7)) (Expr.product (a 8) (a 5)))))))))

def square13High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 5)) (Expr.add (Expr.product (q 7) (n 6)) (Expr.add (Expr.product (n 7) (q 6)) (Expr.add (Expr.product (n 8) (q 5)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 6) (a 7)) (Expr.product (a 8) (a 5))) (Expr.add (Expr.product (a 6) (a 7)) (Expr.product (a 8) (a 5)))))))))

def square13Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := ((UInt256.shiftRight (((q 8) * (n 5)) + (((n 6) * (q 7)) + (((n 7) * (q 6)) + (((n 8) * (q 5)) + (carry + ((((a 6) * (a 7)) + ((a 8) * (a 5))) + (((a 6) * (a 7)) + ((a 8) * (a 5))))))))) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod ((UInt256.mulMod (q 8) (n 5) P) + ((UInt256.mulMod (q 7) (n 6) P) + ((UInt256.mulMod (n 7) (q 6) P) + ((UInt256.mulMod (n 8) (q 5) P) + (carry + (((UInt256.mulMod (a 6) (a 7) P) + (UInt256.mulMod (a 8) (a 5) P)) + ((UInt256.mulMod (a 6) (a 7) P) + (UInt256.mulMod (a 8) (a 5) P)))))))) (UInt256.lnot (((q 8) * (n 5)) + (((n 6) * (q 7)) + (((n 7) * (q 6)) + (((n 8) * (q 5)) + (carry + ((((a 6) * (a 7)) + ((a 8) * (a 5))) + (((a 6) * (a 7)) + ((a 8) * (a 5)))))))))) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

theorem square13_sameValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square13High carry inv a b n q).value = (square13Low carry inv a b n q).value := by
  simp only [square13Low, square13High, Expr.value] <;> ring
def square13Digit (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((q 8) * (n 5)) + (((n 6) * (q 7)) + (((n 7) * (q 6)) + (((n 8) * (q 5)) + (carry + ((((a 6) * (a 7)) + ((a 8) * (a 5))) + (((a 6) * (a 7)) + ((a 8) * (a 5))))))))))
def square13DigitLow (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 5)) (Expr.add (Expr.product (n 6) (q 7)) (Expr.add (Expr.product (n 7) (q 6)) (Expr.add (Expr.product (n 8) (q 5)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 6) (a 7)) (Expr.product (a 8) (a 5))) (Expr.add (Expr.product (a 6) (a 7)) (Expr.product (a 8) (a 5)))))))))
theorem square13_digitValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square13DigitLow carry inv a b n q).value = (square13High carry inv a b n q).value := by
  simp only [square13DigitLow, square13High, Expr.value] <;> ring
theorem square13_digit (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square13Digit carry inv a b n q).toNat = (square13High carry inv a b n q).value % radix := by
  rw [← square13_digitValue]
  unfold square13Digit
  exact digitValue (square13DigitLow carry inv a b n q)

theorem square13_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square13High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (square13High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (q 8) (n 5) radix (hq 8 (by decide)) (hn 5 (by decide)), ⟨productBound (q 7) (n 6) radix (hq 7 (by decide)) (hn 6 (by decide)), ⟨productBound (n 7) (q 6) radix (hn 7 (by decide)) (hq 6 (by decide)), ⟨productBound (n 8) (q 5) radix (hn 8 (by decide)) (hq 5 (by decide)), ⟨True.intro, ⟨⟨productBound (a 6) (a 7) radix (ha 6 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 5) radix (ha 8 (by decide)) (ha 5 (by decide))⟩, ⟨productBound (a 6) (a 7) radix (ha 6 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 5) radix (ha 8 (by decide)) (ha 5 (by decide))⟩⟩⟩⟩⟩⟩⟩
  have hl : (square13High carry inv a b n q).literalsBounded carry.toNat := by
    simp [square13High, Expr.literalsBounded]
  have hv := valueBound (square13High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (square13High carry inv a b n q).products ≤ 18 := by norm_num [square13High, Expr.products]
  have hlc : (square13High carry inv a b n q).literals ≤ 1 := by norm_num [square13High, Expr.literals]
  calc
    _ ≤ (square13High carry inv a b n q).products*((radix-1)^2) + (square13High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem square13_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((square13High carry inv a b n q).high P).toNat % residueModulus = (square13High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (square13High carry inv a b n q)
    (by norm_num [square13High, Expr.count])
    (by simp [square13High, Expr.literalsBounded, hcp])).2

theorem square13_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square13Carry carry inv a b n q).toNat = (square13High carry inv a b n q).value / radix := by
  have hs := square13_sameValue carry inv a b n q
  have hh := square13_residue carry inv a b n q hc
  have hl : (square13Low carry inv a b n q).low.toNat = (square13High carry inv a b n q).value % wordRadix := by
    rw [hs]; exact lowValue _
  have hr := rounded_contract ((square13High carry inv a b n q).high P) (square13Low carry inv a b n q).low
    (square13High carry inv a b n q).value carry.toNat hc (square13_bound carry inv a b n q ha hb hn hq hc) hl hh
  exact hr

theorem square13_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square13High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 13 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 13 := by
  simp only [square13High, Expr.value, CycleSubmission.Convolution.column13] <;> ring
end CycleSubmission.Columns
