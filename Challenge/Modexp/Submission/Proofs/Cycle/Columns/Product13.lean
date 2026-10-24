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

def product13Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 5) (q 8)) (Expr.add (Expr.product (n 6) (q 7)) (Expr.add (Expr.product (n 7) (q 6)) (Expr.add (Expr.product (n 8) (q 5)) (Expr.add (Expr.product (b 5) (a 8)) (Expr.add (Expr.product (b 6) (a 7)) (Expr.add (Expr.product (b 7) (a 6)) (Expr.add (Expr.product (b 8) (a 5)) (Expr.literal carry)))))))))

def product13High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 5) (q 8)) (Expr.add (Expr.product (n 6) (q 7)) (Expr.add (Expr.product (n 7) (q 6)) (Expr.add (Expr.product (n 8) (q 5)) (Expr.add (Expr.product (b 5) (a 8)) (Expr.add (Expr.product (b 6) (a 7)) (Expr.add (Expr.product (b 7) (a 6)) (Expr.add (Expr.product (b 8) (a 5)) (Expr.literal carry)))))))))

def product13Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := ((UInt256.shiftRight (((n 5) * (q 8)) + (((n 6) * (q 7)) + (((n 7) * (q 6)) + (((n 8) * (q 5)) + (((b 5) * (a 8)) + (((b 6) * (a 7)) + (((b 7) * (a 6)) + (((b 8) * (a 5)) + carry)))))))) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod ((UInt256.mulMod (n 5) (q 8) P) + ((UInt256.mulMod (n 6) (q 7) P) + ((UInt256.mulMod (n 7) (q 6) P) + ((UInt256.mulMod (n 8) (q 5) P) + ((UInt256.mulMod (b 5) (a 8) P) + ((UInt256.mulMod (b 6) (a 7) P) + ((UInt256.mulMod (b 7) (a 6) P) + ((UInt256.mulMod (b 8) (a 5) P) + carry)))))))) (UInt256.lnot (((n 5) * (q 8)) + (((n 6) * (q 7)) + (((n 7) * (q 6)) + (((n 8) * (q 5)) + (((b 5) * (a 8)) + (((b 6) * (a 7)) + (((b 7) * (a 6)) + (((b 8) * (a 5)) + carry))))))))) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

theorem product13_sameValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product13High carry inv a b n q).value = (product13Low carry inv a b n q).value := by
  simp only [product13Low, product13High, Expr.value] <;> ring
def product13Digit (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((n 5) * (q 8)) + (((n 6) * (q 7)) + (((n 7) * (q 6)) + (((n 8) * (q 5)) + (((b 5) * (a 8)) + (((b 6) * (a 7)) + (((b 7) * (a 6)) + (((b 8) * (a 5)) + carry)))))))))
def product13DigitLow (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 5) (q 8)) (Expr.add (Expr.product (n 6) (q 7)) (Expr.add (Expr.product (n 7) (q 6)) (Expr.add (Expr.product (n 8) (q 5)) (Expr.add (Expr.product (b 5) (a 8)) (Expr.add (Expr.product (b 6) (a 7)) (Expr.add (Expr.product (b 7) (a 6)) (Expr.add (Expr.product (b 8) (a 5)) (Expr.literal carry)))))))))
theorem product13_digitValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product13DigitLow carry inv a b n q).value = (product13High carry inv a b n q).value := by
  simp only [product13DigitLow, product13High, Expr.value] <;> ring
theorem product13_digit (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product13Digit carry inv a b n q).toNat = (product13High carry inv a b n q).value % radix := by
  rw [← product13_digitValue]
  unfold product13Digit
  exact digitValue (product13DigitLow carry inv a b n q)

theorem product13_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (product13High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (product13High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 5) (q 8) radix (hn 5 (by decide)) (hq 8 (by decide)), ⟨productBound (n 6) (q 7) radix (hn 6 (by decide)) (hq 7 (by decide)), ⟨productBound (n 7) (q 6) radix (hn 7 (by decide)) (hq 6 (by decide)), ⟨productBound (n 8) (q 5) radix (hn 8 (by decide)) (hq 5 (by decide)), ⟨productBound (b 5) (a 8) radix (hb 5 (by decide)) (ha 8 (by decide)), ⟨productBound (b 6) (a 7) radix (hb 6 (by decide)) (ha 7 (by decide)), ⟨productBound (b 7) (a 6) radix (hb 7 (by decide)) (ha 6 (by decide)), ⟨productBound (b 8) (a 5) radix (hb 8 (by decide)) (ha 5 (by decide)), True.intro⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (product13High carry inv a b n q).literalsBounded carry.toNat := by
    simp [product13High, Expr.literalsBounded]
  have hv := valueBound (product13High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (product13High carry inv a b n q).products ≤ 18 := by norm_num [product13High, Expr.products]
  have hlc : (product13High carry inv a b n q).literals ≤ 1 := by norm_num [product13High, Expr.literals]
  calc
    _ ≤ (product13High carry inv a b n q).products*((radix-1)^2) + (product13High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem product13_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((product13High carry inv a b n q).high P).toNat % residueModulus = (product13High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (product13High carry inv a b n q)
    (by norm_num [product13High, Expr.count])
    (by simp [product13High, Expr.literalsBounded, hcp])).2

theorem product13_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (product13Carry carry inv a b n q).toNat = (product13High carry inv a b n q).value / radix := by
  have hs := product13_sameValue carry inv a b n q
  have hh := product13_residue carry inv a b n q hc
  have hl : (product13Low carry inv a b n q).low.toNat = (product13High carry inv a b n q).value % wordRadix := by
    rw [hs]; exact lowValue _
  have hr := rounded_contract ((product13High carry inv a b n q).high P) (product13Low carry inv a b n q).low
    (product13High carry inv a b n q).value carry.toNat hc (product13_bound carry inv a b n q ha hb hn hq hc) hl hh
  exact hr

theorem product13_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product13High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (b i).toNat) 13 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 13 := by
  simp only [product13High, Expr.value, CycleSubmission.Convolution.column13] <;> ring
end CycleSubmission.Columns
