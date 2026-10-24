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

def square11Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 3)) (Expr.add (Expr.product (n 4) (q 7)) (Expr.add (Expr.product (q 6) (n 5)) (Expr.add (Expr.product (q 5) (n 6)) (Expr.add (Expr.product (n 7) (q 4)) (Expr.add (Expr.product (n 8) (q 3)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 5) (a 6)) (Expr.add (Expr.product (a 4) (a 7)) (Expr.product (a 8) (a 3)))) (Expr.add (Expr.product (a 5) (a 6)) (Expr.add (Expr.product (a 4) (a 7)) (Expr.product (a 8) (a 3))))))))))))

def square11High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 3)) (Expr.add (Expr.product (q 7) (n 4)) (Expr.add (Expr.product (q 6) (n 5)) (Expr.add (Expr.product (q 5) (n 6)) (Expr.add (Expr.product (n 7) (q 4)) (Expr.add (Expr.product (n 8) (q 3)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 5) (a 6)) (Expr.add (Expr.product (a 4) (a 7)) (Expr.product (a 8) (a 3)))) (Expr.add (Expr.product (a 5) (a 6)) (Expr.add (Expr.product (a 4) (a 7)) (Expr.product (a 8) (a 3))))))))))))

def square11Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := ((UInt256.shiftRight (((q 8) * (n 3)) + (((n 4) * (q 7)) + (((q 6) * (n 5)) + (((q 5) * (n 6)) + (((n 7) * (q 4)) + (((n 8) * (q 3)) + (carry + ((((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))) + (((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))))))))))) (UInt256.ofNat 240)) + (UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod ((UInt256.mulMod (q 8) (n 3) P) + ((UInt256.mulMod (q 7) (n 4) P) + ((UInt256.mulMod (q 6) (n 5) P) + ((UInt256.mulMod (q 5) (n 6) P) + ((UInt256.mulMod (n 7) (q 4) P) + ((UInt256.mulMod (n 8) (q 3) P) + (carry + (((UInt256.mulMod (a 5) (a 6) P) + ((UInt256.mulMod (a 4) (a 7) P) + (UInt256.mulMod (a 8) (a 3) P))) + ((UInt256.mulMod (a 5) (a 6) P) + ((UInt256.mulMod (a 4) (a 7) P) + (UInt256.mulMod (a 8) (a 3) P))))))))))) (UInt256.lnot (((q 8) * (n 3)) + (((n 4) * (q 7)) + (((q 6) * (n 5)) + (((q 5) * (n 6)) + (((n 7) * (q 4)) + (((n 8) * (q 3)) + (carry + ((((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))) + (((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3))))))))))))) P) (UInt256.ofNat 5)) (UInt256.ofNat 16)))

theorem square11_sameValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square11High carry inv a b n q).value = (square11Low carry inv a b n q).value := by
  simp only [square11Low, square11High, Expr.value] <;> ring
def square11Digit (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((q 8) * (n 3)) + (((n 4) * (q 7)) + (((q 6) * (n 5)) + (((q 5) * (n 6)) + (((n 7) * (q 4)) + (((n 8) * (q 3)) + (carry + ((((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))) + (((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))))))))))))
def square11DigitLow (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 8) (n 3)) (Expr.add (Expr.product (n 4) (q 7)) (Expr.add (Expr.product (q 6) (n 5)) (Expr.add (Expr.product (q 5) (n 6)) (Expr.add (Expr.product (n 7) (q 4)) (Expr.add (Expr.product (n 8) (q 3)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 5) (a 6)) (Expr.add (Expr.product (a 4) (a 7)) (Expr.product (a 8) (a 3)))) (Expr.add (Expr.product (a 5) (a 6)) (Expr.add (Expr.product (a 4) (a 7)) (Expr.product (a 8) (a 3))))))))))))
theorem square11_digitValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square11DigitLow carry inv a b n q).value = (square11High carry inv a b n q).value := by
  simp only [square11DigitLow, square11High, Expr.value] <;> ring
theorem square11_digit (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square11Digit carry inv a b n q).toNat = (square11High carry inv a b n q).value % radix := by
  rw [← square11_digitValue]
  unfold square11Digit
  exact digitValue (square11DigitLow carry inv a b n q)

theorem square11_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square11High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (square11High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (q 8) (n 3) radix (hq 8 (by decide)) (hn 3 (by decide)), ⟨productBound (q 7) (n 4) radix (hq 7 (by decide)) (hn 4 (by decide)), ⟨productBound (q 6) (n 5) radix (hq 6 (by decide)) (hn 5 (by decide)), ⟨productBound (q 5) (n 6) radix (hq 5 (by decide)) (hn 6 (by decide)), ⟨productBound (n 7) (q 4) radix (hn 7 (by decide)) (hq 4 (by decide)), ⟨productBound (n 8) (q 3) radix (hn 8 (by decide)) (hq 3 (by decide)), ⟨True.intro, ⟨⟨productBound (a 5) (a 6) radix (ha 5 (by decide)) (ha 6 (by decide)), ⟨productBound (a 4) (a 7) radix (ha 4 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 3) radix (ha 8 (by decide)) (ha 3 (by decide))⟩⟩, ⟨productBound (a 5) (a 6) radix (ha 5 (by decide)) (ha 6 (by decide)), ⟨productBound (a 4) (a 7) radix (ha 4 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 3) radix (ha 8 (by decide)) (ha 3 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (square11High carry inv a b n q).literalsBounded carry.toNat := by
    simp [square11High, Expr.literalsBounded]
  have hv := valueBound (square11High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (square11High carry inv a b n q).products ≤ 18 := by norm_num [square11High, Expr.products]
  have hlc : (square11High carry inv a b n q).literals ≤ 1 := by norm_num [square11High, Expr.literals]
  calc
    _ ≤ (square11High carry inv a b n q).products*((radix-1)^2) + (square11High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem square11_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((square11High carry inv a b n q).high P).toNat % residueModulus = (square11High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (square11High carry inv a b n q)
    (by norm_num [square11High, Expr.count])
    (by simp [square11High, Expr.literalsBounded, hcp])).2

theorem square11_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square11Carry carry inv a b n q).toNat = (square11High carry inv a b n q).value / radix := by
  have hs := square11_sameValue carry inv a b n q
  have hh := square11_residue carry inv a b n q hc
  have hl : (square11Low carry inv a b n q).low.toNat = (square11High carry inv a b n q).value % wordRadix := by
    rw [hs]; exact lowValue _
  have hr := rounded_contract ((square11High carry inv a b n q).high P) (square11Low carry inv a b n q).low
    (square11High carry inv a b n q).value carry.toNat hc (square11_bound carry inv a b n q ha hb hn hq hc) hl hh
  exact hr

theorem square11_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square11High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 11 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 11 := by
  simp only [square11High, Expr.value, CycleSubmission.Convolution.column11] <;> ring
end CycleSubmission.Columns
