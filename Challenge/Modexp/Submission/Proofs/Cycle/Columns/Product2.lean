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

def product2Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 1) (n 1)) (Expr.add (Expr.product (q 0) (n 2)) (Expr.add (Expr.product (b 0) (a 2)) (Expr.add (Expr.product (b 1) (a 1)) (Expr.add (Expr.product (b 2) (a 0)) (Expr.literal carry))))))

def product2High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 2) (n 0)) (Expr.add (Expr.product (q 1) (n 1)) (Expr.add (Expr.product (q 0) (n 2)) (Expr.add (Expr.product (b 0) (a 2)) (Expr.add (Expr.product (b 1) (a 1)) (Expr.add (Expr.product (b 2) (a 0)) (Expr.literal carry)))))))

def product2Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (q 2) (n 0) P) + ((UInt256.mulMod (q 1) (n 1) P) + ((UInt256.mulMod (q 0) (n 2) P) + ((UInt256.mulMod (b 0) (a 2) P) + ((UInt256.mulMod (b 1) (a 1) P) + ((UInt256.mulMod (b 2) (a 0) P) + carry)))))) P)

def product2Q (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((q 1) * (n 1)) + (((q 0) * (n 2)) + (((b 0) * (a 2)) + (((b 1) * (a 1)) + (((b 2) * (a 0)) + carry))))) * inv))
theorem product2_quotient (carry inv : UInt256) (a b n q : Nat → UInt256) :
    product2Q carry inv a b n q = quotient (product2Low carry inv a b n q) inv := by
  have he := maskedDigit_commute (product2Low carry inv a b n q).low inv 240 240
  rw [HistoricalSearch.CRTMaskElision.mask_mul_mask _ _ 240 240 (by decide) (by decide)] at he
  change UInt256.land (UInt256.ofNat (2^240-1)) ((product2Low carry inv a b n q).low * inv) = _
  rw [mul_comm (product2Low carry inv a b n q).low inv]
  exact he
theorem product2_qbound (carry inv : UInt256) (a b n q : Nat → UInt256) : (product2Q carry inv a b n q).toNat < radix := by
  rw [product2_quotient]
  exact quotientBound (product2Low carry inv a b n q) inv
theorem product2_post (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product2High carry inv a b n q).value = (product2Low carry inv a b n q).value + (q 2).toNat*(n 0).toNat := by
  simp only [product2Low, product2High, Expr.value] <;> ring

theorem product2_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (product2High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (product2High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (q 2) (n 0) radix (hq 2 (by decide)) (hn 0 (by decide)), ⟨productBound (q 1) (n 1) radix (hq 1 (by decide)) (hn 1 (by decide)), ⟨productBound (q 0) (n 2) radix (hq 0 (by decide)) (hn 2 (by decide)), ⟨productBound (b 0) (a 2) radix (hb 0 (by decide)) (ha 2 (by decide)), ⟨productBound (b 1) (a 1) radix (hb 1 (by decide)) (ha 1 (by decide)), ⟨productBound (b 2) (a 0) radix (hb 2 (by decide)) (ha 0 (by decide)), True.intro⟩⟩⟩⟩⟩⟩
  have hl : (product2High carry inv a b n q).literalsBounded carry.toNat := by
    simp [product2High, Expr.literalsBounded]
  have hv := valueBound (product2High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (product2High carry inv a b n q).products ≤ 18 := by norm_num [product2High, Expr.products]
  have hlc : (product2High carry inv a b n q).literals ≤ 1 := by norm_num [product2High, Expr.literals]
  calc
    _ ≤ (product2High carry inv a b n q).products*((radix-1)^2) + (product2High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem product2_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((product2High carry inv a b n q).high P).toNat % residueModulus = (product2High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (product2High carry inv a b n q)
    (by norm_num [product2High, Expr.count])
    (by simp [product2High, Expr.literalsBounded, hcp])).2

theorem product2_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1))
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hi : (N*inv.toNat+1) % 2^256 = 0)
    (hnew : q 2 = product2Q carry inv a b n q) :
    (product2Carry carry inv a b n q).toNat = (product2High carry inv a b n q).value / radix ∧
    (product2High carry inv a b n q).value % radix = 0 := by
  have hz := (maskedDigitCancels (product2Low carry inv a b n q).low inv 240 240
    (product2Low carry inv a b n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue (product2Low carry inv a b n q)) hn0 hi).2.1
  have hzero : (product2High carry inv a b n q).value % radix = 0 := by
    rw [product2_post, hnew, product2_quotient]
    exact hz
  refine ⟨?_, hzero⟩
  have hp : 0 < P.toNat := by rw [pValue]; norm_num [residueModulus]
  change (UInt256.mulMod (UInt256.ofNat 2048) ((product2High carry inv a b n q).high P) P).toNat = _
  rw [mulMod_toNat _ _ _ hp, pValue]
  change (2048 * ((product2High carry inv a b n q).high P).toNat) % residueModulus = _
  rw [Nat.mul_comm 2048]
  exact CycleSubmission.Bounds.cancelledRecovery _ carry.toNat _ hc
    (product2_bound carry inv a b n q ha hb hn hq hc) (product2_residue carry inv a b n q hc) hzero

theorem product2_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product2High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (b i).toNat) 2 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 2 := by
  simp only [product2High, Expr.value, CycleSubmission.Convolution.column2] <;> ring
end CycleSubmission.Columns
