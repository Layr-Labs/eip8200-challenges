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

def square0Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.product (a 0) (a 0))

def square0High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 0)) (Expr.product (a 0) (a 0)))

def square0Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (n 0) (q 0) P) + (UInt256.mulMod (a 0) (a 0) P)) P)

def square0Q (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (inv * ((a 0) * (a 0))))
theorem square0_quotient (carry inv : UInt256) (a b n q : Nat → UInt256) :
    square0Q carry inv a b n q = quotient (square0Low carry inv a b n q) inv := by
  have he := maskedDigit_commute (square0Low carry inv a b n q).low inv 240 240
  rw [HistoricalSearch.CRTMaskElision.mask_mul_mask _ _ 240 240 (by decide) (by decide)] at he
  change UInt256.land (UInt256.ofNat (2^240-1)) (inv * (square0Low carry inv a b n q).low) = _
  exact he
theorem square0_qbound (carry inv : UInt256) (a b n q : Nat → UInt256) : (square0Q carry inv a b n q).toNat < radix := by
  rw [square0_quotient]
  exact quotientBound (square0Low carry inv a b n q) inv
theorem square0_post (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square0High carry inv a b n q).value = (square0Low carry inv a b n q).value + (q 0).toNat*(n 0).toNat := by
  simp only [square0Low, square0High, Expr.value] <;> ring

theorem square0_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square0High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (square0High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 0) radix (hn 0 (by decide)) (hq 0 (by decide)), productBound (a 0) (a 0) radix (ha 0 (by decide)) (ha 0 (by decide))⟩
  have hl : (square0High carry inv a b n q).literalsBounded carry.toNat := by
    simp [square0High, Expr.literalsBounded]
  have hv := valueBound (square0High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (square0High carry inv a b n q).products ≤ 18 := by norm_num [square0High, Expr.products]
  have hlc : (square0High carry inv a b n q).literals ≤ 1 := by norm_num [square0High, Expr.literals]
  calc
    _ ≤ (square0High carry inv a b n q).products*((radix-1)^2) + (square0High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem square0_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((square0High carry inv a b n q).high P).toNat % residueModulus = (square0High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (square0High carry inv a b n q)
    (by norm_num [square0High, Expr.count])
    (by simp [square0High, Expr.literalsBounded, hcp])).2

theorem square0_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1))
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hi : (N*inv.toNat+1) % 2^256 = 0)
    (hnew : q 0 = square0Q carry inv a b n q) :
    (square0Carry carry inv a b n q).toNat = (square0High carry inv a b n q).value / radix ∧
    (square0High carry inv a b n q).value % radix = 0 := by
  have hz := (maskedDigitCancels (square0Low carry inv a b n q).low inv 240 240
    (square0Low carry inv a b n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue (square0Low carry inv a b n q)) hn0 hi).2.1
  have hzero : (square0High carry inv a b n q).value % radix = 0 := by
    rw [square0_post, hnew, square0_quotient]
    exact hz
  refine ⟨?_, hzero⟩
  have hp : 0 < P.toNat := by rw [pValue]; norm_num [residueModulus]
  change (UInt256.mulMod (UInt256.ofNat 2048) ((square0High carry inv a b n q).high P) P).toNat = _
  rw [mulMod_toNat _ _ _ hp, pValue]
  change (2048 * ((square0High carry inv a b n q).high P).toNat) % residueModulus = _
  rw [Nat.mul_comm 2048]
  exact CycleSubmission.Bounds.cancelledRecovery _ carry.toNat _ hc
    (square0_bound carry inv a b n q ha hb hn hq hc) (square0_residue carry inv a b n q hc) hzero

theorem square0_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square0High carry inv a b n q).value = 0 +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 0 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 0 := by
  simp only [square0High, Expr.value, CycleSubmission.Convolution.column0] <;> ring
end CycleSubmission.Columns
