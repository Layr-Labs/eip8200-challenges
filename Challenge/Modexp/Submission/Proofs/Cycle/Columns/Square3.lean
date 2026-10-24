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

def square3Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 2) (n 1)) (Expr.add (Expr.product (q 1) (n 2)) (Expr.add (Expr.product (q 0) (n 3)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 1) (a 2)) (Expr.product (a 3) (a 0))) (Expr.add (Expr.product (a 1) (a 2)) (Expr.product (a 3) (a 0))))))))

def square3High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 3) (n 0)) (Expr.add (Expr.product (q 2) (n 1)) (Expr.add (Expr.product (q 1) (n 2)) (Expr.add (Expr.product (q 0) (n 3)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 1) (a 2)) (Expr.product (a 3) (a 0))) (Expr.add (Expr.product (a 1) (a 2)) (Expr.product (a 3) (a 0)))))))))

def square3Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (q 3) (n 0) P) + ((UInt256.mulMod (q 2) (n 1) P) + ((UInt256.mulMod (q 1) (n 2) P) + ((UInt256.mulMod (q 0) (n 3) P) + (carry + (((UInt256.mulMod (a 1) (a 2) P) + (UInt256.mulMod (a 3) (a 0) P)) + ((UInt256.mulMod (a 1) (a 2) P) + (UInt256.mulMod (a 3) (a 0) P)))))))) P)

def square3Q (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((q 2) * (n 1)) + (((q 1) * (n 2)) + (((q 0) * (n 3)) + (carry + ((((a 1) * (a 2)) + ((a 3) * (a 0))) + (((a 1) * (a 2)) + ((a 3) * (a 0)))))))) * inv))
theorem square3_quotient (carry inv : UInt256) (a b n q : Nat → UInt256) :
    square3Q carry inv a b n q = quotient (square3Low carry inv a b n q) inv := by
  have he := maskedDigit_commute (square3Low carry inv a b n q).low inv 240 240
  rw [HistoricalSearch.CRTMaskElision.mask_mul_mask _ _ 240 240 (by decide) (by decide)] at he
  change UInt256.land (UInt256.ofNat (2^240-1)) ((square3Low carry inv a b n q).low * inv) = _
  rw [mul_comm (square3Low carry inv a b n q).low inv]
  exact he
theorem square3_qbound (carry inv : UInt256) (a b n q : Nat → UInt256) : (square3Q carry inv a b n q).toNat < radix := by
  rw [square3_quotient]
  exact quotientBound (square3Low carry inv a b n q) inv
theorem square3_post (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square3High carry inv a b n q).value = (square3Low carry inv a b n q).value + (q 3).toNat*(n 0).toNat := by
  simp only [square3Low, square3High, Expr.value] <;> ring

theorem square3_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square3High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (square3High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (q 3) (n 0) radix (hq 3 (by decide)) (hn 0 (by decide)), ⟨productBound (q 2) (n 1) radix (hq 2 (by decide)) (hn 1 (by decide)), ⟨productBound (q 1) (n 2) radix (hq 1 (by decide)) (hn 2 (by decide)), ⟨productBound (q 0) (n 3) radix (hq 0 (by decide)) (hn 3 (by decide)), ⟨True.intro, ⟨⟨productBound (a 1) (a 2) radix (ha 1 (by decide)) (ha 2 (by decide)), productBound (a 3) (a 0) radix (ha 3 (by decide)) (ha 0 (by decide))⟩, ⟨productBound (a 1) (a 2) radix (ha 1 (by decide)) (ha 2 (by decide)), productBound (a 3) (a 0) radix (ha 3 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩
  have hl : (square3High carry inv a b n q).literalsBounded carry.toNat := by
    simp [square3High, Expr.literalsBounded]
  have hv := valueBound (square3High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (square3High carry inv a b n q).products ≤ 18 := by norm_num [square3High, Expr.products]
  have hlc : (square3High carry inv a b n q).literals ≤ 1 := by norm_num [square3High, Expr.literals]
  calc
    _ ≤ (square3High carry inv a b n q).products*((radix-1)^2) + (square3High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem square3_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((square3High carry inv a b n q).high P).toNat % residueModulus = (square3High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (square3High carry inv a b n q)
    (by norm_num [square3High, Expr.count])
    (by simp [square3High, Expr.literalsBounded, hcp])).2

theorem square3_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1))
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hi : (N*inv.toNat+1) % 2^256 = 0)
    (hnew : q 3 = square3Q carry inv a b n q) :
    (square3Carry carry inv a b n q).toNat = (square3High carry inv a b n q).value / radix ∧
    (square3High carry inv a b n q).value % radix = 0 := by
  have hz := (maskedDigitCancels (square3Low carry inv a b n q).low inv 240 240
    (square3Low carry inv a b n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue (square3Low carry inv a b n q)) hn0 hi).2.1
  have hzero : (square3High carry inv a b n q).value % radix = 0 := by
    rw [square3_post, hnew, square3_quotient]
    exact hz
  refine ⟨?_, hzero⟩
  have hp : 0 < P.toNat := by rw [pValue]; norm_num [residueModulus]
  change (UInt256.mulMod (UInt256.ofNat 2048) ((square3High carry inv a b n q).high P) P).toNat = _
  rw [mulMod_toNat _ _ _ hp, pValue]
  change (2048 * ((square3High carry inv a b n q).high P).toNat) % residueModulus = _
  rw [Nat.mul_comm 2048]
  exact CycleSubmission.Bounds.cancelledRecovery _ carry.toNat _ hc
    (square3_bound carry inv a b n q ha hb hn hq hc) (square3_residue carry inv a b n q hc) hzero

theorem square3_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square3High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 3 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 3 := by
  simp only [square3High, Expr.value, CycleSubmission.Convolution.column3] <;> ring
end CycleSubmission.Columns
