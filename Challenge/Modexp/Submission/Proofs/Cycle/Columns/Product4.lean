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

def product4Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 3) (n 1)) (Expr.add (Expr.product (q 2) (n 2)) (Expr.add (Expr.product (q 1) (n 3)) (Expr.add (Expr.product (q 0) (n 4)) (Expr.add (Expr.product (b 0) (a 4)) (Expr.add (Expr.product (b 1) (a 3)) (Expr.add (Expr.product (b 2) (a 2)) (Expr.add (Expr.product (b 3) (a 1)) (Expr.add (Expr.product (b 4) (a 0)) (Expr.literal carry))))))))))

def product4High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 4) (n 0)) (Expr.add (Expr.product (q 3) (n 1)) (Expr.add (Expr.product (q 2) (n 2)) (Expr.add (Expr.product (q 1) (n 3)) (Expr.add (Expr.product (q 0) (n 4)) (Expr.add (Expr.product (b 0) (a 4)) (Expr.add (Expr.product (b 1) (a 3)) (Expr.add (Expr.product (b 2) (a 2)) (Expr.add (Expr.product (b 3) (a 1)) (Expr.add (Expr.product (b 4) (a 0)) (Expr.literal carry)))))))))))

def product4Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (q 4) (n 0) P) + ((UInt256.mulMod (q 3) (n 1) P) + ((UInt256.mulMod (q 2) (n 2) P) + ((UInt256.mulMod (q 1) (n 3) P) + ((UInt256.mulMod (q 0) (n 4) P) + ((UInt256.mulMod (b 0) (a 4) P) + ((UInt256.mulMod (b 1) (a 3) P) + ((UInt256.mulMod (b 2) (a 2) P) + ((UInt256.mulMod (b 3) (a 1) P) + ((UInt256.mulMod (b 4) (a 0) P) + carry)))))))))) P)

def product4Q (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) ((((q 3) * (n 1)) + (((q 2) * (n 2)) + (((q 1) * (n 3)) + (((q 0) * (n 4)) + (((b 0) * (a 4)) + (((b 1) * (a 3)) + (((b 2) * (a 2)) + (((b 3) * (a 1)) + (((b 4) * (a 0)) + carry))))))))) * inv))
theorem product4_quotient (carry inv : UInt256) (a b n q : Nat → UInt256) :
    product4Q carry inv a b n q = quotient (product4Low carry inv a b n q) inv := by
  have he := maskedDigit_commute (product4Low carry inv a b n q).low inv 240 240
  rw [HistoricalSearch.CRTMaskElision.mask_mul_mask _ _ 240 240 (by decide) (by decide)] at he
  change UInt256.land (UInt256.ofNat (2^240-1)) ((product4Low carry inv a b n q).low * inv) = _
  rw [mul_comm (product4Low carry inv a b n q).low inv]
  exact he
theorem product4_qbound (carry inv : UInt256) (a b n q : Nat → UInt256) : (product4Q carry inv a b n q).toNat < radix := by
  rw [product4_quotient]
  exact quotientBound (product4Low carry inv a b n q) inv
theorem product4_post (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product4High carry inv a b n q).value = (product4Low carry inv a b n q).value + (q 4).toNat*(n 0).toNat := by
  simp only [product4Low, product4High, Expr.value] <;> ring

theorem product4_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (product4High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (product4High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (q 4) (n 0) radix (hq 4 (by decide)) (hn 0 (by decide)), ⟨productBound (q 3) (n 1) radix (hq 3 (by decide)) (hn 1 (by decide)), ⟨productBound (q 2) (n 2) radix (hq 2 (by decide)) (hn 2 (by decide)), ⟨productBound (q 1) (n 3) radix (hq 1 (by decide)) (hn 3 (by decide)), ⟨productBound (q 0) (n 4) radix (hq 0 (by decide)) (hn 4 (by decide)), ⟨productBound (b 0) (a 4) radix (hb 0 (by decide)) (ha 4 (by decide)), ⟨productBound (b 1) (a 3) radix (hb 1 (by decide)) (ha 3 (by decide)), ⟨productBound (b 2) (a 2) radix (hb 2 (by decide)) (ha 2 (by decide)), ⟨productBound (b 3) (a 1) radix (hb 3 (by decide)) (ha 1 (by decide)), ⟨productBound (b 4) (a 0) radix (hb 4 (by decide)) (ha 0 (by decide)), True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (product4High carry inv a b n q).literalsBounded carry.toNat := by
    simp [product4High, Expr.literalsBounded]
  have hv := valueBound (product4High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (product4High carry inv a b n q).products ≤ 18 := by norm_num [product4High, Expr.products]
  have hlc : (product4High carry inv a b n q).literals ≤ 1 := by norm_num [product4High, Expr.literals]
  calc
    _ ≤ (product4High carry inv a b n q).products*((radix-1)^2) + (product4High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem product4_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((product4High carry inv a b n q).high P).toNat % residueModulus = (product4High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (product4High carry inv a b n q)
    (by norm_num [product4High, Expr.count])
    (by simp [product4High, Expr.literalsBounded, hcp])).2

theorem product4_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1))
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hi : (N*inv.toNat+1) % 2^256 = 0)
    (hnew : q 4 = product4Q carry inv a b n q) :
    (product4Carry carry inv a b n q).toNat = (product4High carry inv a b n q).value / radix ∧
    (product4High carry inv a b n q).value % radix = 0 := by
  have hz := (maskedDigitCancels (product4Low carry inv a b n q).low inv 240 240
    (product4Low carry inv a b n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue (product4Low carry inv a b n q)) hn0 hi).2.1
  have hzero : (product4High carry inv a b n q).value % radix = 0 := by
    rw [product4_post, hnew, product4_quotient]
    exact hz
  refine ⟨?_, hzero⟩
  have hp : 0 < P.toNat := by rw [pValue]; norm_num [residueModulus]
  change (UInt256.mulMod (UInt256.ofNat 2048) ((product4High carry inv a b n q).high P) P).toNat = _
  rw [mulMod_toNat _ _ _ hp, pValue]
  change (2048 * ((product4High carry inv a b n q).high P).toNat) % residueModulus = _
  rw [Nat.mul_comm 2048]
  exact CycleSubmission.Bounds.cancelledRecovery _ carry.toNat _ hc
    (product4_bound carry inv a b n q ha hb hn hq hc) (product4_residue carry inv a b n q hc) hzero

theorem product4_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product4High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (b i).toNat) 4 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 4 := by
  simp only [product4High, Expr.value, CycleSubmission.Convolution.column4] <;> ring
end CycleSubmission.Columns
