import Challenge.Modexp.Submission.Proofs.Cycle.WordArithmetic
import Challenge.Modexp.Submission.Proofs.CRT.CRTWordBridge
import Challenge.Modexp.Submission.Proofs.CRT.RoundedWordBridge
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096

/-!
# Word-level bridges between the r5 kernels and the leader's column contracts

The r5 kernels compute the same column words as the leader's radix-2^240 cycle kernel, with
three differences in form: the quotient is `(inv' * L) >> 16` with `inv' = ninv << 16`
instead of `maskedDigit L ninv 240 240`; the residue of `q*n0` is added before (not after)
the column terms; and the high-column `ADDMOD` takes `~L` first. The lemmas below rewrite the
r5 forms into `WordArithmetic.cancelledCarry` and `RoundedWordBridge.carryWord`.
-/

namespace CycleSubmission.R5.Words
open EvmSemantics
open Challenge.EvmProof.Word
open HistoricalSearch.CRTColumn HistoricalSearch.ProductAccumulate HistoricalSearch.CRTWordBridge
open HistoricalSearch.ColumnExpressions HistoricalSearch.WordCancellation
open CycleSubmission.WordArithmetic

theorem mulMod_comm (a b n : UInt256) : UInt256.mulMod a b n = UInt256.mulMod b a n := by
  unfold UInt256.mulMod; rw [Nat.mul_comm]

theorem addMod_comm (a b n : UInt256) : UInt256.addMod a b n = UInt256.addMod b a n := by
  unfold UInt256.addMod; rw [Nat.add_comm]

theorem add_comm' (a b : UInt256) : a + b = b + a := by
  apply word_ext
  rw [word_toNat_add, word_toNat_add, Nat.add_comm]

theorem shiftRight16_toNat (a : UInt256) :
    (UInt256.shiftRight a (UInt256.ofNat 16)).toNat = a.toNat / 2^16 := by
  rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by decide : 16 < 256), Nat.shiftRight_eq_div_pow]

/-- `((x*2^16 mod 2^256)*y mod 2^256) / 2^16 = x*y mod 2^240`. -/
theorem shifted_product (x y : Nat) :
    ((x * 2^16 % 2^256) * y % 2^256) / 2^16 = (y * x) % 2^240 := by
  have h1 : (x * 2^16 % 2^256) * y % 2^256 = ((y * x) % 2^240) * 2^16 := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [show x * 2^16 * y = (y * x) * 2^16 by ring,
      show (2^256 : Nat) = 2^240 * 2^16 by norm_num, Nat.mul_mod_mul_right]
  rw [h1, Nat.mul_div_cancel _ (Nat.two_pow_pos 16)]

/-- The r5 quotient with the shifted inverse is the leader's masked quotient. -/
theorem quotient_shifted (ninv L : UInt256) :
    UInt256.shiftRight (UInt256.shiftLeft ninv (UInt256.ofNat 16) * L) (UInt256.ofNat 16) =
      maskedDigit L ninv 240 240 := by
  apply word_ext
  rw [shiftRight16_toNat, mul_toNat, shiftLeft_toNat _ 16 (by decide), Nat.shiftLeft_eq,
    maskedDigit_toNat L ninv 240 240 L.toNat (by decide) (by decide)
      (Nat.mod_eq_of_lt L.val.isLt).symm]
  exact shifted_product _ _

/-- Low column carry: r5 form → `cancelledCarry`. -/
theorem low_carry (e : Expr) (ninv n0 : UInt256) :
    UInt256.mulMod (UInt256.ofNat 2048)
        (UInt256.mulMod (UInt256.shiftRight (UInt256.shiftLeft ninv (UInt256.ofNat 16) * e.low)
          (UInt256.ofNat 16)) n0 P + e.high P) P =
      cancelledCarry e ninv n0 := by
  rw [quotient_shifted, mulMod_comm (UInt256.ofNat 2048), add_comm']
  rfl

/-- High column carry: r5 form → `RoundedWordBridge.carryWord`. -/
theorem high_carry (lo H : UInt256) :
    UInt256.shiftRight lo (UInt256.ofNat 240) +
        UInt256.shiftLeft (UInt256.shiftRight (UInt256.addMod (UInt256.lnot lo) H P)
          (UInt256.ofNat 5)) (UInt256.ofNat 16) =
      HistoricalSearch.RoundedWordBridge.carryWord H lo P (UInt256.ofNat 240) (UInt256.ofNat 16) := by
  unfold HistoricalSearch.RoundedWordBridge.carryWord
  rw [addMod_comm (UInt256.lnot lo)]

/-- The PUSH30 mask literal. -/
theorem mask_literal :
    (UInt256.ofNat 1766847064778384329583297500742918515827483896875618958121606201292619775) =
      UInt256.ofNat (2^240 - 1) := by norm_num

end CycleSubmission.R5.Words
