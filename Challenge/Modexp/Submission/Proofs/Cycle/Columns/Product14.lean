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

def product14Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 6) (q 8)) (Expr.add (Expr.product (n 7) (q 7)) (Expr.add (Expr.product (n 8) (q 6)) (Expr.add (Expr.product (b 6) (a 8)) (Expr.add (Expr.product (b 7) (a 7)) (Expr.add (Expr.product (b 8) (a 6)) (Expr.literal carry)))))))

def product14High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 6) (q 8)) (Expr.add (Expr.product (n 7) (q 7)) (Expr.add (Expr.product (n 8) (q 6)) (Expr.add (Expr.product (b 6) (a 8)) (Expr.add (Expr.product (b 7) (a 7)) (Expr.add (Expr.product (b 8) (a 6)) (Expr.literal carry)))))))

def product14Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := ((UInt256.shiftRight (((n 6) * (q 8)) + (((n 7) * (q 7)) + (((n 8) * (q 6)) + (((b 6) * (a 8)) + (((b 7) * (a 7)) + (((b 8) * (a 6)) + carry)))))) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod ((UInt256.mulMod (n 6) (q 8) P) + ((UInt256.mulMod (n 7) (q 7) P) + ((UInt256.mulMod (n 8) (q 6) P) + ((UInt256.mulMod (b 6) (a 8) P) + ((UInt256.mulMod (b 7) (a 7) P) + ((UInt256.mulMod (b 8) (a 6) P) + carry)))))) (UInt256.lnot (((n 6) * (q 8)) + (((n 7) * (q 7)) + (((n 8) * (q 6)) + (((b 6) * (a 8)) + (((b 7) * (a 7)) + (((b 8) * (a 6)) + carry))))))) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

theorem product14_sameValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product14High carry inv a b n q).value = (product14Low carry inv a b n q).value := by
  simp only [product14Low, product14High, Expr.value] <;> ring
def product14Digit (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((n 6) * (q 8)) + (((n 7) * (q 7)) + (((n 8) * (q 6)) + (((b 6) * (a 8)) + (((b 7) * (a 7)) + (((b 8) * (a 6)) + carry)))))))
def product14DigitLow (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 6) (q 8)) (Expr.add (Expr.product (n 7) (q 7)) (Expr.add (Expr.product (n 8) (q 6)) (Expr.add (Expr.product (b 6) (a 8)) (Expr.add (Expr.product (b 7) (a 7)) (Expr.add (Expr.product (b 8) (a 6)) (Expr.literal carry)))))))
theorem product14_digitValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product14DigitLow carry inv a b n q).value = (product14High carry inv a b n q).value := by
  simp only [product14DigitLow, product14High, Expr.value] <;> ring
theorem product14_digit (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product14Digit carry inv a b n q).toNat = (product14High carry inv a b n q).value % radix := by
  rw [← product14_digitValue]
  unfold product14Digit
  exact digitValue (product14DigitLow carry inv a b n q)

theorem product14_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (product14High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (product14High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 6) (q 8) radix (hn 6 (by decide)) (hq 8 (by decide)), ⟨productBound (n 7) (q 7) radix (hn 7 (by decide)) (hq 7 (by decide)), ⟨productBound (n 8) (q 6) radix (hn 8 (by decide)) (hq 6 (by decide)), ⟨productBound (b 6) (a 8) radix (hb 6 (by decide)) (ha 8 (by decide)), ⟨productBound (b 7) (a 7) radix (hb 7 (by decide)) (ha 7 (by decide)), ⟨productBound (b 8) (a 6) radix (hb 8 (by decide)) (ha 6 (by decide)), True.intro⟩⟩⟩⟩⟩⟩
  have hl : (product14High carry inv a b n q).literalsBounded carry.toNat := by
    simp [product14High, Expr.literalsBounded]
  have hv := valueBound (product14High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (product14High carry inv a b n q).products ≤ 18 := by norm_num [product14High, Expr.products]
  have hlc : (product14High carry inv a b n q).literals ≤ 1 := by norm_num [product14High, Expr.literals]
  calc
    _ ≤ (product14High carry inv a b n q).products*((radix-1)^2) + (product14High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem product14_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((product14High carry inv a b n q).high P).toNat % residueModulus = (product14High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (product14High carry inv a b n q)
    (by norm_num [product14High, Expr.count])
    (by simp [product14High, Expr.literalsBounded, hcp])).2

theorem product14_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (product14Carry carry inv a b n q).toNat = (product14High carry inv a b n q).value / radix := by
  have hs := product14_sameValue carry inv a b n q
  have hh := product14_residue carry inv a b n q hc
  have hl : (product14Low carry inv a b n q).low.toNat = (product14High carry inv a b n q).value % wordRadix := by
    rw [hs]; exact lowValue _
  have hr := rounded_contract ((product14High carry inv a b n q).high P) (product14Low carry inv a b n q).low
    (product14High carry inv a b n q).value carry.toNat hc (product14_bound carry inv a b n q ha hb hn hq hc) hl hh
  exact hr

theorem product14_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product14High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (b i).toNat) 14 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 14 := by
  simp only [product14High, Expr.value, CycleSubmission.Convolution.column14] <;> ring
end CycleSubmission.Columns
