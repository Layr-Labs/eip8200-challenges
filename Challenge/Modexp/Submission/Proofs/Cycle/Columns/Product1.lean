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

def product1Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 0) (n 1)) (Expr.add (Expr.product (b 0) (a 1)) (Expr.add (Expr.product (b 1) (a 0)) (Expr.literal carry))))

def product1High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 1) (n 0)) (Expr.add (Expr.product (q 0) (n 1)) (Expr.add (Expr.product (b 0) (a 1)) (Expr.add (Expr.product (b 1) (a 0)) (Expr.literal carry)))))

def product1Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (q 1) (n 0) P) + ((UInt256.mulMod (q 0) (n 1) P) + ((UInt256.mulMod (b 0) (a 1) P) + ((UInt256.mulMod (b 1) (a 0) P) + carry)))) P)

def product1Q (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((q 0) * (n 1)) + (((b 0) * (a 1)) + (((b 1) * (a 0)) + carry))) * inv))
theorem product1_quotient (carry inv : UInt256) (a b n q : Nat → UInt256) :
    product1Q carry inv a b n q = quotient (product1Low carry inv a b n q) inv := by
  have he := maskedDigit_commute (product1Low carry inv a b n q).low inv 240 240
  rw [HistoricalSearch.CRTMaskElision.mask_mul_mask _ _ 240 240 (by decide) (by decide)] at he
  change UInt256.land (UInt256.ofNat (2^240-1)) ((product1Low carry inv a b n q).low * inv) = _
  rw [mul_comm (product1Low carry inv a b n q).low inv]
  exact he
theorem product1_qbound (carry inv : UInt256) (a b n q : Nat → UInt256) : (product1Q carry inv a b n q).toNat < radix := by
  rw [product1_quotient]
  exact quotientBound (product1Low carry inv a b n q) inv
theorem product1_post (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product1High carry inv a b n q).value = (product1Low carry inv a b n q).value + (q 1).toNat*(n 0).toNat := by
  simp only [product1Low, product1High, Expr.value] <;> ring

theorem product1_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (product1High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (product1High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (q 1) (n 0) radix (hq 1 (by decide)) (hn 0 (by decide)), ⟨productBound (q 0) (n 1) radix (hq 0 (by decide)) (hn 1 (by decide)), ⟨productBound (b 0) (a 1) radix (hb 0 (by decide)) (ha 1 (by decide)), ⟨productBound (b 1) (a 0) radix (hb 1 (by decide)) (ha 0 (by decide)), True.intro⟩⟩⟩⟩
  have hl : (product1High carry inv a b n q).literalsBounded carry.toNat := by
    simp [product1High, Expr.literalsBounded]
  have hv := valueBound (product1High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (product1High carry inv a b n q).products ≤ 18 := by norm_num [product1High, Expr.products]
  have hlc : (product1High carry inv a b n q).literals ≤ 1 := by norm_num [product1High, Expr.literals]
  calc
    _ ≤ (product1High carry inv a b n q).products*((radix-1)^2) + (product1High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem product1_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((product1High carry inv a b n q).high P).toNat % residueModulus = (product1High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (product1High carry inv a b n q)
    (by norm_num [product1High, Expr.count])
    (by simp [product1High, Expr.literalsBounded, hcp])).2

theorem product1_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1))
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hi : (N*inv.toNat+1) % 2^256 = 0)
    (hnew : q 1 = product1Q carry inv a b n q) :
    (product1Carry carry inv a b n q).toNat = (product1High carry inv a b n q).value / radix ∧
    (product1High carry inv a b n q).value % radix = 0 := by
  have hz := (maskedDigitCancels (product1Low carry inv a b n q).low inv 240 240
    (product1Low carry inv a b n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue (product1Low carry inv a b n q)) hn0 hi).2.1
  have hzero : (product1High carry inv a b n q).value % radix = 0 := by
    rw [product1_post, hnew, product1_quotient]
    exact hz
  refine ⟨?_, hzero⟩
  have hp : 0 < P.toNat := by rw [pValue]; norm_num [residueModulus]
  change (UInt256.mulMod (UInt256.ofNat 2048) ((product1High carry inv a b n q).high P) P).toNat = _
  rw [mulMod_toNat _ _ _ hp, pValue]
  change (2048 * ((product1High carry inv a b n q).high P).toNat) % residueModulus = _
  rw [Nat.mul_comm 2048]
  exact CycleSubmission.Bounds.cancelledRecovery _ carry.toNat _ hc
    (product1_bound carry inv a b n q ha hb hn hq hc) (product1_residue carry inv a b n q hc) hzero

theorem product1_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product1High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (b i).toNat) 1 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 1 := by
  simp only [product1High, Expr.value, CycleSubmission.Convolution.column1] <;> ring
end CycleSubmission.Columns
