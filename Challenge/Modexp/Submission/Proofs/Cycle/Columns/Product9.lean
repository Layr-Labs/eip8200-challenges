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

def product9Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 8)) (Expr.add (Expr.product (q 7) (n 2)) (Expr.add (Expr.product (n 3) (q 6)) (Expr.add (Expr.product (n 4) (q 5)) (Expr.add (Expr.product (n 5) (q 4)) (Expr.add (Expr.product (n 6) (q 3)) (Expr.add (Expr.product (n 7) (q 2)) (Expr.add (Expr.product (n 8) (q 1)) (Expr.add (Expr.product (b 1) (a 8)) (Expr.add (Expr.product (b 2) (a 7)) (Expr.add (Expr.product (b 3) (a 6)) (Expr.add (Expr.product (b 4) (a 5)) (Expr.add (Expr.product (b 5) (a 4)) (Expr.add (Expr.product (b 6) (a 3)) (Expr.add (Expr.product (b 7) (a 2)) (Expr.add (Expr.product (b 8) (a 1)) (Expr.literal carry)))))))))))))))))

def product9High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 8)) (Expr.add (Expr.product (q 7) (n 2)) (Expr.add (Expr.product (q 6) (n 3)) (Expr.add (Expr.product (n 4) (q 5)) (Expr.add (Expr.product (n 5) (q 4)) (Expr.add (Expr.product (n 6) (q 3)) (Expr.add (Expr.product (n 7) (q 2)) (Expr.add (Expr.product (n 8) (q 1)) (Expr.add (Expr.product (b 1) (a 8)) (Expr.add (Expr.product (b 2) (a 7)) (Expr.add (Expr.product (b 3) (a 6)) (Expr.add (Expr.product (b 4) (a 5)) (Expr.add (Expr.product (b 5) (a 4)) (Expr.add (Expr.product (b 6) (a 3)) (Expr.add (Expr.product (b 7) (a 2)) (Expr.add (Expr.product (b 8) (a 1)) (Expr.literal carry)))))))))))))))))

def product9Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (CycleSubmission.DirectRecovery.carry ((UInt256.mulMod (n 1) (q 8) P) + ((UInt256.mulMod (q 7) (n 2) P) + ((UInt256.mulMod (q 6) (n 3) P) + ((UInt256.mulMod (n 4) (q 5) P) + ((UInt256.mulMod (n 5) (q 4) P) + ((UInt256.mulMod (n 6) (q 3) P) + ((UInt256.mulMod (n 7) (q 2) P) + ((UInt256.mulMod (n 8) (q 1) P) + ((UInt256.mulMod (b 1) (a 8) P) + ((UInt256.mulMod (b 2) (a 7) P) + ((UInt256.mulMod (b 3) (a 6) P) + ((UInt256.mulMod (b 4) (a 5) P) + ((UInt256.mulMod (b 5) (a 4) P) + ((UInt256.mulMod (b 6) (a 3) P) + ((UInt256.mulMod (b 7) (a 2) P) + ((UInt256.mulMod (b 8) (a 1) P) + carry)))))))))))))))) (((n 1) * (q 8)) + (((q 7) * (n 2)) + (((n 3) * (q 6)) + (((n 4) * (q 5)) + (((n 5) * (q 4)) + (((n 6) * (q 3)) + (((n 7) * (q 2)) + (((n 8) * (q 1)) + (((b 1) * (a 8)) + (((b 2) * (a 7)) + (((b 3) * (a 6)) + (((b 4) * (a 5)) + (((b 5) * (a 4)) + (((b 6) * (a 3)) + (((b 7) * (a 2)) + (((b 8) * (a 1)) + carry)))))))))))))))))

theorem product9_sameValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product9High carry inv a b n q).value = (product9Low carry inv a b n q).value := by
  simp only [product9Low, product9High, Expr.value] <;> ring
def product9Digit (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (((n 1) * (q 8)) + (((q 7) * (n 2)) + (((n 3) * (q 6)) + (((n 4) * (q 5)) + (((n 5) * (q 4)) + (((n 6) * (q 3)) + (((n 7) * (q 2)) + (((n 8) * (q 1)) + (((b 1) * (a 8)) + (((b 2) * (a 7)) + (((b 3) * (a 6)) + (((b 4) * (a 5)) + (((b 5) * (a 4)) + (((b 6) * (a 3)) + (((b 7) * (a 2)) + (((b 8) * (a 1)) + carry)))))))))))))))))
def product9DigitLow (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 8)) (Expr.add (Expr.product (q 7) (n 2)) (Expr.add (Expr.product (n 3) (q 6)) (Expr.add (Expr.product (n 4) (q 5)) (Expr.add (Expr.product (n 5) (q 4)) (Expr.add (Expr.product (n 6) (q 3)) (Expr.add (Expr.product (n 7) (q 2)) (Expr.add (Expr.product (n 8) (q 1)) (Expr.add (Expr.product (b 1) (a 8)) (Expr.add (Expr.product (b 2) (a 7)) (Expr.add (Expr.product (b 3) (a 6)) (Expr.add (Expr.product (b 4) (a 5)) (Expr.add (Expr.product (b 5) (a 4)) (Expr.add (Expr.product (b 6) (a 3)) (Expr.add (Expr.product (b 7) (a 2)) (Expr.add (Expr.product (b 8) (a 1)) (Expr.literal carry)))))))))))))))))
theorem product9_digitValue (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product9DigitLow carry inv a b n q).value = (product9High carry inv a b n q).value := by
  simp only [product9DigitLow, product9High, Expr.value] <;> ring
theorem product9_digit (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product9Digit carry inv a b n q).toNat = (product9High carry inv a b n q).value % radix := by
  rw [← product9_digitValue]
  unfold product9Digit
  exact digitValue (product9DigitLow carry inv a b n q)

theorem product9_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (product9High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (product9High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 1) (q 8) radix (hn 1 (by decide)) (hq 8 (by decide)), ⟨productBound (q 7) (n 2) radix (hq 7 (by decide)) (hn 2 (by decide)), ⟨productBound (q 6) (n 3) radix (hq 6 (by decide)) (hn 3 (by decide)), ⟨productBound (n 4) (q 5) radix (hn 4 (by decide)) (hq 5 (by decide)), ⟨productBound (n 5) (q 4) radix (hn 5 (by decide)) (hq 4 (by decide)), ⟨productBound (n 6) (q 3) radix (hn 6 (by decide)) (hq 3 (by decide)), ⟨productBound (n 7) (q 2) radix (hn 7 (by decide)) (hq 2 (by decide)), ⟨productBound (n 8) (q 1) radix (hn 8 (by decide)) (hq 1 (by decide)), ⟨productBound (b 1) (a 8) radix (hb 1 (by decide)) (ha 8 (by decide)), ⟨productBound (b 2) (a 7) radix (hb 2 (by decide)) (ha 7 (by decide)), ⟨productBound (b 3) (a 6) radix (hb 3 (by decide)) (ha 6 (by decide)), ⟨productBound (b 4) (a 5) radix (hb 4 (by decide)) (ha 5 (by decide)), ⟨productBound (b 5) (a 4) radix (hb 5 (by decide)) (ha 4 (by decide)), ⟨productBound (b 6) (a 3) radix (hb 6 (by decide)) (ha 3 (by decide)), ⟨productBound (b 7) (a 2) radix (hb 7 (by decide)) (ha 2 (by decide)), ⟨productBound (b 8) (a 1) radix (hb 8 (by decide)) (ha 1 (by decide)), True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (product9High carry inv a b n q).literalsBounded carry.toNat := by
    simp [product9High, Expr.literalsBounded]
  have hv := valueBound (product9High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (product9High carry inv a b n q).products ≤ 18 := by norm_num [product9High, Expr.products]
  have hlc : (product9High carry inv a b n q).literals ≤ 1 := by norm_num [product9High, Expr.literals]
  calc
    _ ≤ (product9High carry inv a b n q).products*((radix-1)^2) + (product9High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem product9_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((product9High carry inv a b n q).high P).toNat % residueModulus = (product9High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (product9High carry inv a b n q)
    (by norm_num [product9High, Expr.count])
    (by simp [product9High, Expr.literalsBounded, hcp])).2

theorem product9_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (product9Carry carry inv a b n q).toNat = (product9High carry inv a b n q).value / radix := by
  have hcp : carry.toNat ≤ HistoricalSearch.CRTColumn.residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact CycleSubmission.DirectRecovery.expression_contract
    (product9High carry inv a b n q) (product9Low carry inv a b n q) carry.toNat
    (by norm_num [product9High, Expr.count])
    (by simp [product9High, Expr.literalsBounded, hcp])
    (product9_sameValue carry inv a b n q) hc
    (product9_bound carry inv a b n q ha hb hn hq hc)

theorem product9_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product9High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (b i).toNat) 9 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 9 := by
  simp only [product9High, Expr.value, CycleSubmission.Convolution.column9] <;> ring
end CycleSubmission.Columns
