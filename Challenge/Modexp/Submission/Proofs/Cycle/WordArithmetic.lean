import Challenge.Modexp.Submission.Proofs.Cycle.SelectedRadix
import Challenge.Modexp.Submission.Proofs.CRT.WordCancellation
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
namespace CycleSubmission.WordArithmetic
open EvmSemantics
open Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.ProductAccumulate
open HistoricalSearch.ColumnExpressions HistoricalSearch.WordCancellation

def radix : Nat := 2^240
def P : UInt256 := UInt256.ofNat residueModulus
def quotient (e : Expr) (inv : UInt256) : UInt256 := maskedDigit e.low inv 240 240
def post (e : Expr) (inv n0 : UInt256) : Expr :=
  .add e (.product (quotient e inv) n0)
def cancelledCarry (e : Expr) (inv n0 : UInt256) : UInt256 :=
  UInt256.mulMod ((post e inv n0).high P) (UInt256.ofNat 2048) P

theorem pValue : P.toNat = residueModulus := by
  norm_num [P, word_toNat_ofNat, residueModulus]

theorem digitValue (e : Expr) :
    (UInt256.land (UInt256.ofNat (2^240-1)) e.low).toNat = e.value % radix := by
  rw [land_comm]
  change (e.low &&& UInt256.ofNat (2^240-1)).toNat = _
  rw [mask_toNat _ 240 (by decide), lowValue]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by decide : 240 ≤ 256))

theorem quotientBound (e : Expr) (inv : UInt256) :
    (quotient e inv).toNat < radix := by
  unfold quotient maskedDigit
  rw [mask_toNat _ 240 (by decide)]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem cancelled_contract (e : Expr) (inv n0 : UInt256) (N C : Nat)
    (hcount : e.count ≤ 18) (hlit : e.literalsBounded C)
    (hc : C ≤ 18*(radix-1))
    (hpre : e.value ≤ 17*(radix-1)^2+C)
    (hn : n0.toNat = N % radix)
    (hinv : (N*inv.toNat+1) % 2^256 = 0) :
    (quotient e inv).toNat < radix ∧
    (post e inv n0).value % radix = 0 ∧
    (cancelledCarry e inv n0).toNat = (post e inv n0).value / radix ∧
    (cancelledCarry e inv n0).toNat ≤ 18*(radix-1) := by
  have hq := maskedDigitCancels e.low inv 240 240 e.value N n0.toNat
    (by decide) (by decide) (lowValue e) hn hinv
  have hqbound : (quotient e inv).toNat < radix := hq.1
  have hnBound : n0.toNat < radix := by
    rw [hn]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hpBound := productBound (quotient e inv) n0 radix hqbound hnBound
  have hs : (post e inv n0).value ≤ 18*(radix-1)^2+C := by
    change e.value + (quotient e inv).toNat*n0.toNat ≤ _
    nlinarith
  have hzero : (post e inv n0).value % radix = 0 := hq.2.1
  have hCP : C ≤ residueModulus-1 := by
    norm_num [radix, residueModulus] at hc ⊢
    omega
  have hmon : ∀ x : Expr, x.literalsBounded C → x.literalsBounded (residueModulus-1) := by
    intro x
    induction x with
    | product a b => exact fun _ => True.intro
    | literal a => exact fun ha => le_trans ha hCP
    | add a b ia ib => exact fun hab => ⟨ia hab.1, ib hab.2⟩
  have hh := highInvariant P pValue (post e inv n0)
    (show (post e inv n0).count ≤ 19 by change e.count+1 ≤ 19; omega)
    (show (post e inv n0).literalsBounded (residueModulus-1) from ⟨hmon e hlit, True.intro⟩)
  have hp : 0 < P.toNat := by rw [pValue]; norm_num [residueModulus]
  have hout : (cancelledCarry e inv n0).toNat = (post e inv n0).value / radix := by
    rw [cancelledCarry, mulMod_toNat _ _ _ hp, pValue]
    change (((post e inv n0).high P).toNat * 2048) % residueModulus = _
    exact CycleSubmission.Bounds.cancelledRecovery _ C _ hc hs hh.2 hzero
  refine ⟨hqbound, hzero, hout, ?_⟩
  rw [hout]
  exact (CycleSubmission.Bounds.fullColumnBounds _ C hc hs).1

theorem rounded_contract (H lo : UInt256) (S C : Nat)
    (hc : C ≤ 18*(radix-1)) (hs : S ≤ 18*(radix-1)^2+C)
    (hlo : lo.toNat = S % wordRadix)
    (hH : H.toNat % residueModulus = S % residueModulus) :
    (HistoricalSearch.RoundedWordBridge.carryWord H lo P
      (UInt256.ofNat 240) (UInt256.ofNat 16)).toNat = S/radix := by
  have h := HistoricalSearch.RoundedWordBridge.carryWord_toNat 240 S C H.toNat
    (by decide) (by decide) hc hs H.val.isLt hH
  have hword : UInt256.ofNat (S % wordRadix) = lo := by
    rw [← hlo]; exact (word_eq_ofNat_toNat lo).symm
  rw [← word_eq_ofNat_toNat H, hword] at h
  exact h

end CycleSubmission.WordArithmetic
