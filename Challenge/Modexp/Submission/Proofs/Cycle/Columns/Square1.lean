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

def square1Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 0) (n 1)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 1) (a 0)) (Expr.product (a 1) (a 0)))))

def square1High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 1) (n 0)) (Expr.add (Expr.product (q 0) (n 1)) (Expr.add (Expr.literal carry) (Expr.add (Expr.product (a 1) (a 0)) (Expr.product (a 1) (a 0))))))

def square1Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (q 1) (n 0) P) + ((UInt256.mulMod (q 0) (n 1) P) + (carry + ((UInt256.mulMod (a 1) (a 0) P) + (UInt256.mulMod (a 1) (a 0) P))))) P)

def square1Q (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((q 0) * (n 1)) + (carry + (((a 1) * (a 0)) + ((a 1) * (a 0))))) * inv))
theorem square1_quotient (carry inv : UInt256) (a b n q : Nat → UInt256) :
    square1Q carry inv a b n q = quotient (square1Low carry inv a b n q) inv := by
  have he := maskedDigit_commute (square1Low carry inv a b n q).low inv 240 240
  rw [HistoricalSearch.CRTMaskElision.mask_mul_mask _ _ 240 240 (by decide) (by decide)] at he
  change UInt256.land (UInt256.ofNat (2^240-1)) ((square1Low carry inv a b n q).low * inv) = _
  rw [mul_comm (square1Low carry inv a b n q).low inv]
  exact he
theorem square1_qbound (carry inv : UInt256) (a b n q : Nat → UInt256) : (square1Q carry inv a b n q).toNat < radix := by
  rw [square1_quotient]
  exact quotientBound (square1Low carry inv a b n q) inv
theorem square1_post (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square1High carry inv a b n q).value = (square1Low carry inv a b n q).value + (q 1).toNat*(n 0).toNat := by
  simp only [square1Low, square1High, Expr.value] <;> ring

theorem square1_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square1High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (square1High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (q 1) (n 0) radix (hq 1 (by decide)) (hn 0 (by decide)), ⟨productBound (q 0) (n 1) radix (hq 0 (by decide)) (hn 1 (by decide)), ⟨True.intro, ⟨productBound (a 1) (a 0) radix (ha 1 (by decide)) (ha 0 (by decide)), productBound (a 1) (a 0) radix (ha 1 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩
  have hl : (square1High carry inv a b n q).literalsBounded carry.toNat := by
    simp [square1High, Expr.literalsBounded]
  have hv := valueBound (square1High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (square1High carry inv a b n q).products ≤ 18 := by norm_num [square1High, Expr.products]
  have hlc : (square1High carry inv a b n q).literals ≤ 1 := by norm_num [square1High, Expr.literals]
  calc
    _ ≤ (square1High carry inv a b n q).products*((radix-1)^2) + (square1High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem square1_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((square1High carry inv a b n q).high P).toNat % residueModulus = (square1High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (square1High carry inv a b n q)
    (by norm_num [square1High, Expr.count])
    (by simp [square1High, Expr.literalsBounded, hcp])).2

theorem square1_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1))
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hi : (N*inv.toNat+1) % 2^256 = 0)
    (hnew : q 1 = square1Q carry inv a b n q) :
    (square1Carry carry inv a b n q).toNat = (square1High carry inv a b n q).value / radix ∧
    (square1High carry inv a b n q).value % radix = 0 := by
  have hz := (maskedDigitCancels (square1Low carry inv a b n q).low inv 240 240
    (square1Low carry inv a b n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue (square1Low carry inv a b n q)) hn0 hi).2.1
  have hzero : (square1High carry inv a b n q).value % radix = 0 := by
    rw [square1_post, hnew, square1_quotient]
    exact hz
  refine ⟨?_, hzero⟩
  have hp : 0 < P.toNat := by rw [pValue]; norm_num [residueModulus]
  change (UInt256.mulMod (UInt256.ofNat 2048) ((square1High carry inv a b n q).high P) P).toNat = _
  rw [mulMod_toNat _ _ _ hp, pValue]
  change (2048 * ((square1High carry inv a b n q).high P).toNat) % residueModulus = _
  rw [Nat.mul_comm 2048]
  exact CycleSubmission.Bounds.cancelledRecovery _ carry.toNat _ hc
    (square1_bound carry inv a b n q ha hb hn hq hc) (square1_residue carry inv a b n q hc) hzero

theorem square1_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square1High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 1 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 1 := by
  simp only [square1High, Expr.value, CycleSubmission.Convolution.column1] <;> ring
end CycleSubmission.Columns
