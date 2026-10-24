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

def product0Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.product (a 0) (b 0))

def product0High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 0)) (Expr.product (a 0) (b 0)))

def product0Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (n 0) (q 0) P) + (UInt256.mulMod (a 0) (b 0) P)) P)

def product0Q (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (inv * ((a 0) * (b 0))))
theorem product0_quotient (carry inv : UInt256) (a b n q : Nat → UInt256) :
    product0Q carry inv a b n q = quotient (product0Low carry inv a b n q) inv := by
  have he := maskedDigit_commute (product0Low carry inv a b n q).low inv 240 240
  rw [HistoricalSearch.CRTMaskElision.mask_mul_mask _ _ 240 240 (by decide) (by decide)] at he
  change UInt256.land (UInt256.ofNat (2^240-1)) (inv * (product0Low carry inv a b n q).low) = _
  exact he
theorem product0_qbound (carry inv : UInt256) (a b n q : Nat → UInt256) : (product0Q carry inv a b n q).toNat < radix := by
  rw [product0_quotient]
  exact quotientBound (product0Low carry inv a b n q) inv
theorem product0_post (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product0High carry inv a b n q).value = (product0Low carry inv a b n q).value + (q 0).toNat*(n 0).toNat := by
  simp only [product0Low, product0High, Expr.value] <;> ring

theorem product0_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (product0High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (product0High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 0) radix (hn 0 (by decide)) (hq 0 (by decide)), productBound (a 0) (b 0) radix (ha 0 (by decide)) (hb 0 (by decide))⟩
  have hl : (product0High carry inv a b n q).literalsBounded carry.toNat := by
    simp [product0High, Expr.literalsBounded]
  have hv := valueBound (product0High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (product0High carry inv a b n q).products ≤ 18 := by norm_num [product0High, Expr.products]
  have hlc : (product0High carry inv a b n q).literals ≤ 1 := by norm_num [product0High, Expr.literals]
  calc
    _ ≤ (product0High carry inv a b n q).products*((radix-1)^2) + (product0High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem product0_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((product0High carry inv a b n q).high P).toNat % residueModulus = (product0High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (product0High carry inv a b n q)
    (by norm_num [product0High, Expr.count])
    (by simp [product0High, Expr.literalsBounded, hcp])).2

theorem product0_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1))
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hi : (N*inv.toNat+1) % 2^256 = 0)
    (hnew : q 0 = product0Q carry inv a b n q) :
    (product0Carry carry inv a b n q).toNat = (product0High carry inv a b n q).value / radix ∧
    (product0High carry inv a b n q).value % radix = 0 := by
  have hz := (maskedDigitCancels (product0Low carry inv a b n q).low inv 240 240
    (product0Low carry inv a b n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue (product0Low carry inv a b n q)) hn0 hi).2.1
  have hzero : (product0High carry inv a b n q).value % radix = 0 := by
    rw [product0_post, hnew, product0_quotient]
    exact hz
  refine ⟨?_, hzero⟩
  have hp : 0 < P.toNat := by rw [pValue]; norm_num [residueModulus]
  change (UInt256.mulMod (UInt256.ofNat 2048) ((product0High carry inv a b n q).high P) P).toNat = _
  rw [mulMod_toNat _ _ _ hp, pValue]
  change (2048 * ((product0High carry inv a b n q).high P).toNat) % residueModulus = _
  rw [Nat.mul_comm 2048]
  exact CycleSubmission.Bounds.cancelledRecovery _ carry.toNat _ hc
    (product0_bound carry inv a b n q ha hb hn hq hc) (product0_residue carry inv a b n q hc) hzero

theorem product0_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product0High carry inv a b n q).value = 0 +
      convolution 9 (fun i => (a i).toNat) (fun i => (b i).toNat) 0 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 0 := by
  simp only [product0High, Expr.value, CycleSubmission.Convolution.column0] <;> ring
end CycleSubmission.Columns
