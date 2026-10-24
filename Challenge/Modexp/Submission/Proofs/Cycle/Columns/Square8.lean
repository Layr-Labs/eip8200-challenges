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

def square8Low (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (q 7) (n 1)) (Expr.add (Expr.product (q 6) (n 2)) (Expr.add (Expr.product (q 5) (n 3)) (Expr.add (Expr.product (q 4) (n 4)) (Expr.add (Expr.product (q 3) (n 5)) (Expr.add (Expr.product (q 2) (n 6)) (Expr.add (Expr.product (n 7) (q 1)) (Expr.add (Expr.product (n 8) (q 0)) (Expr.add (Expr.product (a 4) (a 4)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 3) (a 5)) (Expr.add (Expr.product (a 2) (a 6)) (Expr.add (Expr.product (a 7) (a 1)) (Expr.product (a 8) (a 0))))) (Expr.add (Expr.product (a 3) (a 5)) (Expr.add (Expr.product (a 2) (a 6)) (Expr.add (Expr.product (a 7) (a 1)) (Expr.product (a 8) (a 0))))))))))))))))

def square8High (carry inv : UInt256) (a b n q : Nat → UInt256) : Expr := (Expr.add (Expr.product (n 0) (q 8)) (Expr.add (Expr.product (q 7) (n 1)) (Expr.add (Expr.product (q 6) (n 2)) (Expr.add (Expr.product (q 5) (n 3)) (Expr.add (Expr.product (q 4) (n 4)) (Expr.add (Expr.product (q 3) (n 5)) (Expr.add (Expr.product (q 2) (n 6)) (Expr.add (Expr.product (n 7) (q 1)) (Expr.add (Expr.product (a 4) (a 4)) (Expr.add (Expr.product (n 8) (q 0)) (Expr.add (Expr.literal carry) (Expr.add (Expr.add (Expr.product (a 3) (a 5)) (Expr.add (Expr.product (a 2) (a 6)) (Expr.add (Expr.product (a 1) (a 7)) (Expr.product (a 8) (a 0))))) (Expr.add (Expr.product (a 3) (a 5)) (Expr.add (Expr.product (a 2) (a 6)) (Expr.add (Expr.product (a 1) (a 7)) (Expr.product (a 8) (a 0)))))))))))))))))

def square8Carry (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.mulMod (UInt256.ofNat 2048) ((UInt256.mulMod (n 0) (q 8) P) + ((UInt256.mulMod (q 7) (n 1) P) + ((UInt256.mulMod (q 6) (n 2) P) + ((UInt256.mulMod (q 5) (n 3) P) + ((UInt256.mulMod (q 4) (n 4) P) + ((UInt256.mulMod (q 3) (n 5) P) + ((UInt256.mulMod (q 2) (n 6) P) + ((UInt256.mulMod (n 7) (q 1) P) + ((UInt256.mulMod (a 4) (a 4) P) + ((UInt256.mulMod (n 8) (q 0) P) + (carry + (((UInt256.mulMod (a 3) (a 5) P) + ((UInt256.mulMod (a 2) (a 6) P) + ((UInt256.mulMod (a 1) (a 7) P) + (UInt256.mulMod (a 8) (a 0) P)))) + ((UInt256.mulMod (a 3) (a 5) P) + ((UInt256.mulMod (a 2) (a 6) P) + ((UInt256.mulMod (a 1) (a 7) P) + (UInt256.mulMod (a 8) (a 0) P)))))))))))))))) P)

def square8Q (carry inv : UInt256) (a b n q : Nat → UInt256) : UInt256 := (UInt256.land (UInt256.ofNat (2^240-1)) (inv * (((q 7) * (n 1)) + (((q 6) * (n 2)) + (((q 5) * (n 3)) + (((q 4) * (n 4)) + (((q 3) * (n 5)) + (((q 2) * (n 6)) + (((n 7) * (q 1)) + (((n 8) * (q 0)) + (((a 4) * (a 4)) + (carry + ((((a 3) * (a 5)) + (((a 2) * (a 6)) + (((a 7) * (a 1)) + ((a 8) * (a 0))))) + (((a 3) * (a 5)) + (((a 2) * (a 6)) + (((a 7) * (a 1)) + ((a 8) * (a 0))))))))))))))))))
theorem square8_quotient (carry inv : UInt256) (a b n q : Nat → UInt256) :
    square8Q carry inv a b n q = quotient (square8Low carry inv a b n q) inv := by
  have he := maskedDigit_commute (square8Low carry inv a b n q).low inv 240 240
  rw [HistoricalSearch.CRTMaskElision.mask_mul_mask _ _ 240 240 (by decide) (by decide)] at he
  change UInt256.land (UInt256.ofNat (2^240-1)) (inv * (square8Low carry inv a b n q).low) = _
  exact he
theorem square8_qbound (carry inv : UInt256) (a b n q : Nat → UInt256) : (square8Q carry inv a b n q).toNat < radix := by
  rw [square8_quotient]
  exact quotientBound (square8Low carry inv a b n q) inv
theorem square8_post (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square8High carry inv a b n q).value = (square8Low carry inv a b n q).value + (q 8).toNat*(n 0).toNat := by
  simp only [square8Low, square8High, Expr.value] <;> ring

theorem square8_bound (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1)) :
    (square8High carry inv a b n q).value ≤ 18*(radix-1)^2+carry.toNat := by
  have hp : (square8High carry inv a b n q).productsBounded ((radix-1)^2) := by
    exact ⟨productBound (n 0) (q 8) radix (hn 0 (by decide)) (hq 8 (by decide)), ⟨productBound (q 7) (n 1) radix (hq 7 (by decide)) (hn 1 (by decide)), ⟨productBound (q 6) (n 2) radix (hq 6 (by decide)) (hn 2 (by decide)), ⟨productBound (q 5) (n 3) radix (hq 5 (by decide)) (hn 3 (by decide)), ⟨productBound (q 4) (n 4) radix (hq 4 (by decide)) (hn 4 (by decide)), ⟨productBound (q 3) (n 5) radix (hq 3 (by decide)) (hn 5 (by decide)), ⟨productBound (q 2) (n 6) radix (hq 2 (by decide)) (hn 6 (by decide)), ⟨productBound (n 7) (q 1) radix (hn 7 (by decide)) (hq 1 (by decide)), ⟨productBound (a 4) (a 4) radix (ha 4 (by decide)) (ha 4 (by decide)), ⟨productBound (n 8) (q 0) radix (hn 8 (by decide)) (hq 0 (by decide)), ⟨True.intro, ⟨⟨productBound (a 3) (a 5) radix (ha 3 (by decide)) (ha 5 (by decide)), ⟨productBound (a 2) (a 6) radix (ha 2 (by decide)) (ha 6 (by decide)), ⟨productBound (a 1) (a 7) radix (ha 1 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 0) radix (ha 8 (by decide)) (ha 0 (by decide))⟩⟩⟩, ⟨productBound (a 3) (a 5) radix (ha 3 (by decide)) (ha 5 (by decide)), ⟨productBound (a 2) (a 6) radix (ha 2 (by decide)) (ha 6 (by decide)), ⟨productBound (a 1) (a 7) radix (ha 1 (by decide)) (ha 7 (by decide)), productBound (a 8) (a 0) radix (ha 8 (by decide)) (ha 0 (by decide))⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hl : (square8High carry inv a b n q).literalsBounded carry.toNat := by
    simp [square8High, Expr.literalsBounded]
  have hv := valueBound (square8High carry inv a b n q) ((radix-1)^2) carry.toNat hp hl
  have hpc : (square8High carry inv a b n q).products ≤ 18 := by norm_num [square8High, Expr.products]
  have hlc : (square8High carry inv a b n q).literals ≤ 1 := by norm_num [square8High, Expr.literals]
  calc
    _ ≤ (square8High carry inv a b n q).products*((radix-1)^2) + (square8High carry inv a b n q).literals*carry.toNat := hv
    _ ≤ 18*((radix-1)^2)+1*carry.toNat := Nat.add_le_add
      (Nat.mul_le_mul_right ((radix-1)^2) hpc) (Nat.mul_le_mul_right carry.toNat hlc)
    _ = _ := by rw [Nat.one_mul]
theorem square8_residue (carry inv : UInt256) (a b n q : Nat → UInt256) (hc : carry.toNat ≤ 18*(radix-1)) :
    ((square8High carry inv a b n q).high P).toNat % residueModulus = (square8High carry inv a b n q).value % residueModulus := by
  have hcp : carry.toNat ≤ residueModulus-1 := by
    have h := HistoricalSearch.GenericColumn.carryReductionRedundant 240 carry.toNat (by decide) hc
    omega
  exact (highInvariant P pValue (square8High carry inv a b n q)
    (by norm_num [square8High, Expr.count])
    (by simp [square8High, Expr.literalsBounded, hcp])).2

theorem square8_contract (carry inv : UInt256) (a b n q : Nat → UInt256)
    (ha : ∀ i < 9, (a i).toNat < radix)
    (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (hq : ∀ i < 9, (q i).toNat < radix)
    (hc : carry.toNat ≤ 18*(radix-1))
    (N : Nat) (hn0 : (n 0).toNat = N % radix)
    (hi : (N*inv.toNat+1) % 2^256 = 0)
    (hnew : q 8 = square8Q carry inv a b n q) :
    (square8Carry carry inv a b n q).toNat = (square8High carry inv a b n q).value / radix ∧
    (square8High carry inv a b n q).value % radix = 0 := by
  have hz := (maskedDigitCancels (square8Low carry inv a b n q).low inv 240 240
    (square8Low carry inv a b n q).value N (n 0).toNat (by decide) (by decide)
    (lowValue (square8Low carry inv a b n q)) hn0 hi).2.1
  have hzero : (square8High carry inv a b n q).value % radix = 0 := by
    rw [square8_post, hnew, square8_quotient]
    exact hz
  refine ⟨?_, hzero⟩
  have hp : 0 < P.toNat := by rw [pValue]; norm_num [residueModulus]
  change (UInt256.mulMod (UInt256.ofNat 2048) ((square8High carry inv a b n q).high P) P).toNat = _
  rw [mulMod_toNat _ _ _ hp, pValue]
  change (2048 * ((square8High carry inv a b n q).high P).toNat) % residueModulus = _
  rw [Nat.mul_comm 2048]
  exact CycleSubmission.Bounds.cancelledRecovery _ carry.toNat _ hc
    (square8_bound carry inv a b n q ha hb hn hq hc) (square8_residue carry inv a b n q hc) hzero

theorem square8_convolution (carry inv : UInt256) (a b n q : Nat → UInt256) :
    (square8High carry inv a b n q).value = carry.toNat +
      convolution 9 (fun i => (a i).toNat) (fun i => (a i).toNat) 8 +
      convolution 9 (fun i => (q i).toNat) (fun i => (n i).toNat) 8 := by
  simp only [square8High, Expr.value, CycleSubmission.Convolution.column8] <;> ring
end CycleSubmission.Columns
