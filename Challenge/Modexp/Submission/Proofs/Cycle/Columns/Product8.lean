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

def product8Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 1) (q 7)) (Expr.add (Expr.product (q 6) (n 2)) (Expr.add (Expr.product (n 3) (q 5)) (Expr.add (Expr.product (n 4) (q 4)) (Expr.add (Expr.product (n 5) (q 3)) (Expr.add (Expr.product (n 6) (q 2)) (Expr.add (Expr.product (n 7) (q 1)) (Expr.add (Expr.product (n 8) (q 0)) (Expr.add (Expr.product (b 0) (a 8)) (Expr.add (Expr.product (b 1) (a 7)) (Expr.add (Expr.product (b 2) (a 6)) (Expr.add (Expr.product (b 3) (a 5)) (Expr.add (Expr.product (b 4) (a 4)) (Expr.add (Expr.product (b 5) (a 3)) (Expr.add (Expr.product (b 6) (a 2)) (Expr.add (Expr.product (b 7) (a 1)) (Expr.add (Expr.product (b 8) (a 0)) (Expr.literal carry))))))))))))))))))

def product8High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 8)) (Expr.add (Expr.product (n 1) (q 7)) (Expr.add (Expr.product (q 6) (n 2)) (Expr.add (Expr.product (q 5) (n 3)) (Expr.add (Expr.product (n 4) (q 4)) (Expr.add (Expr.product (n 5) (q 3)) (Expr.add (Expr.product (n 6) (q 2)) (Expr.add (Expr.product (n 7) (q 1)) (Expr.add (Expr.product (n 8) (q 0)) (Expr.add (Expr.product (b 0) (a 8)) (Expr.add (Expr.product (b 1) (a 7)) (Expr.add (Expr.product (b 2) (a 6)) (Expr.add (Expr.product (b 3) (a 5)) (Expr.add (Expr.product (b 4) (a 4)) (Expr.add (Expr.product (b 5) (a 3)) (Expr.add (Expr.product (b 6) (a 2)) (Expr.add (Expr.product (b 7) (a 1)) (Expr.add (Expr.product (b 8) (a 0)) (Expr.literal carry)))))))))))))))))))

def product8Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (n 0) (q 8) P) + ((UInt256.mulMod (n 1) (q 7) P) + ((UInt256.mulMod (q 6) (n 2) P) + ((UInt256.mulMod (q 5) (n 3) P) + ((UInt256.mulMod (n 4) (q 4) P) + ((UInt256.mulMod (n 5) (q 3) P) + ((UInt256.mulMod (n 6) (q 2) P) + ((UInt256.mulMod (n 7) (q 1) P) + ((UInt256.mulMod (n 8) (q 0) P) + ((UInt256.mulMod (b 0) (a 8) P) + ((UInt256.mulMod (b 1) (a 7) P) + ((UInt256.mulMod (b 2) (a 6) P) + ((UInt256.mulMod (b 3) (a 5) P) + ((UInt256.mulMod (b 4) (a 4) P) + ((UInt256.mulMod (b 5) (a 3) P) + ((UInt256.mulMod (b 6) (a 2) P) + ((UInt256.mulMod (b 7) (a 1) P) + ((UInt256.mulMod (b 8) (a 0) P) + carry)))))))))))))))))) P)

def product8Q (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land ((((n 1) * (q 7)) + (((q 6) * (n 2)) + (((n 3) * (q 5)) + (((n 4) * (q 4)) + (((n 5) * (q 3)) + (((n 6) * (q 2)) + (((n 7) * (q 1)) + (((n 8) * (q 0)) + (((b 0) * (a 8)) + (((b 1) * (a 7)) + (((b 2) * (a 6)) + (((b 3) * (a 5)) + (((b 4) * (a 4)) + (((b 5) * (a 3)) + (((b 6) * (a 2)) + (((b 7) * (a 1)) + (((b 8) * (a 0)) + carry))))))))))))))))) * inv) (UInt256.ofNat (2^240-1)))
theorem product8_quotient (carry inv : UInt256) (a b n q : Nat → UInt256) :
    product8Q carry inv a b n q = quotient (product8Low carry inv a b n q) inv := by
  have he := maskedDigit_commute (product8Low carry inv a b n q).low inv 240 240
  rw [HistoricalSearch.CRTMaskElision.mask_mul_mask _ _ 240 240 (by decide) (by decide)] at he
  change UInt256.land ((product8Low carry inv a b n q).low * inv) (UInt256.ofNat (2^240-1)) = _
  rw [land_comm, mul_comm (product8Low carry inv a b n q).low inv]
  exact he
theorem product8_qbound (carry inv : UInt256) (a b n q : Nat → UInt256) : (product8Q carry inv a b n q).toNat < radix := by
  rw [product8_quotient]
  exact quotientBound (product8Low carry inv a b n q) inv
theorem product8_post (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product8High carry inv a b n q).value = (product8Low carry inv a b n q).value + (q 8).toNat*(n 0).toNat := by
  simp only [product8Low, product8High, Expr.value] <;> ring

theorem product8_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (product8High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (product8High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 8) radix (hn 0 (by decide)) (hq 8 (by decide)), ⟨productBound (n 1) (q 7) radix (hn 1 (by decide)) (hq 7 (by decide)), ⟨productBound (q 6) (n 2) radix (hq 6 (by decide)) (hn 2 (by decide)), ⟨productBound (q 5) (n 3) radix (hq 5 (by decide)) (hn 3 (by decide)), ⟨productBound (n 4) (q 4) radix (hn 4 (by decide)) (hq 4 (by decide)), ⟨productBound (n 5) (q 3) radix (hn 5 (by decide)) (hq 3 (by decide)), ⟨productBound (n 6) (q 2) radix (hn 6 (by decide)) (hq 2 (by decide)), ⟨productBound (n 7) (q 1) radix (hn 7 (by decide)) (hq 1 (by decide)), ⟨productBound (n 8) (q 0) radix (hn 8 (by decide)) (hq 0 (by decide)), ⟨productBound (b 0) (a 8) radix (hb 0 (by decide)) (ha 8 (by decide)), ⟨productBound (b 1) (a 7) radix (hb 1 (by decide)) (ha 7 (by decide)), ⟨productBound (b 2) (a 6) radix (hb 2 (by decide)) (ha 6 (by decide)), ⟨productBound (b 3) (a 5) radix (hb 3 (by decide)) (ha 5 (by decide)), ⟨productBound (b 4) (a 4) radix (hb 4 (by decide)) (ha 4 (by decide)), ⟨productBound (b 5) (a 3) radix (hb 5 (by decide)) (ha 3 (by decide)), ⟨productBound (b 6) (a 2) radix (hb 6 (by decide)) (ha 2 (by decide)), ⟨productBound (b 7) (a 1) radix (hb 7 (by decide)) (ha 1 (by decide)), ⟨productBound (b 8) (a 0) radix (hb 8 (by decide)) (ha 0 (by decide)), True.intro⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (product8High carry inv a b n q).literalsBounded carry.toNat := by
    simp [product8High, Expr.literalsBounded]
  have hv := valueBound (product8High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (product8High carry inv a b n q).products ≤ 18 := by norm_num [product8High, Expr.products]
  have hlc : (product8High carry inv a b n q).literals ≤ 1 := by norm_num [product8High, Expr.literals]
  calc
    _ ≤ (product8High carry inv a b n q).products*((radix-1)^2) + (product8High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem product8_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((product8High carry inv a b n q).high P).toNat % residueModulus = (product8High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (product8High carry inv a b n q)
    (by norm_num [product8High, Expr.count])
    (by simp [product8High, Expr.literalsBounded, hcp])).2

theorem product8_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1))
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hi : (N*inv.toNat+1) % 2^256 = 0)
    (hnew : q 8 = product8Q carry inv a b n q) :
    (product8Carry carry inv a b n q).toNat = (product8High carry inv a b n q).value / radix ∧
    (product8High carry inv a b n q).value % radix = 0 := by
  have hz := (maskedDigitCancels (product8Low carry inv a b n q).low inv 240 240
    (product8Low carry inv a b n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue (product8Low carry inv a b n q)) hn0 hi).2.1
  have hzero : (product8High carry inv a b n q).value % radix = 0 := by
    rw [product8_post, hnew, product8_quotient]
    exact hz
  refine ⟨?_, hzero⟩
  have hp : 0 < P.toNat := by rw [pValue]; norm_num [residueModulus]
  change (UInt256.mulMod (UInt256.ofNat 2048) ((product8High carry inv a b n q).high P) P).toNat = _
  rw [mulMod_toNat _ _ _ hp, pValue]
  change (2048 * ((product8High carry inv a b n q).high P).toNat) % residueModulus = _
  rw [Nat.mul_comm 2048]
  exact CycleSubmission.Bounds.cancelledRecovery _ carry.toNat _ hc
    (product8_bound carry inv a b n q ha hb hn hq hc) (product8_residue carry inv a b n q hc) hzero

theorem product8_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (product8High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (b i).toNat) 8 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 8 := by
  simp only [product8High, Expr.value, CycleSubmission.Convolution.column8] <;> ring
end CycleSubmission.Columns
