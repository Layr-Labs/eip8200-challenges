import Challenge.Modexp.Submission.Proofs.CRT.CRTInputMemory
import Challenge.Modexp.Submission.Proofs.Cycle.InputWords
import Challenge.Modexp.Submission.Proofs.R5.Words
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-!
# Digit windows of the r5 prologue

A 1024-bit value `X` stored as four big-endian words at `base` (`Model.FastRepresents mem base
4 X`) is unpacked into five 240-bit digits with one `MLOAD` each:

* `X`'s digit `i < 4`: the window at `base + 96 - 30 i`, masked to 240 bits;
* its top digit: the first word shifted right by 192;
* `X * 2^176`'s digits `1 ≤ i < 4`: the window at `base + 118 - 30 i`, masked;
  its digit 0: the last word shifted left by 176, masked; its top digit: the first word
  shifted right by 16.
-/

namespace CycleSubmission.R5.Digits
open EvmSemantics Challenge.EvmProof.Word
open HistoricalSearch.CRTInputMemory HistoricalSearch.WordCancellation HistoricalSearch.MixedMontgomery
open Challenge.Modexp.Submission.Proofs
open CycleSubmission.WordArithmetic

def M : UInt256 := UInt256.ofNat (2^240 - 1)

theorem land_M_toNat (w : UInt256) : (UInt256.land M w).toNat = w.toNat % 2^240 := by
  unfold M
  rw [land_comm]
  change (w &&& UInt256.ofNat (2^240-1)).toNat = _
  exact mask_toNat _ 240 (by decide)

theorem window {mem : ByteArray} {base X : Nat} (h : Fast.Model.FastRepresents mem base 4 X)
    (lead suffix : Nat) (hb : lead + 32 + suffix = 128) :
    (UInt256.land M (MachineState.readWord mem (base + lead))).toNat = X / 2^(8*suffix) % 2^240 := by
  rw [land_M_toNat]
  have hu := unaligned_digit (lead := lead) (suffix := suffix) (shift := 0) (width := 240) h
    (by omega) (by decide)
  simpa only [Nat.pow_zero, Nat.div_one, Nat.add_zero] using hu

theorem first_word {mem : ByteArray} {base X : Nat} (h : Fast.Model.FastRepresents mem base 4 X) :
    (MachineState.readWord mem base).toNat = X / 2^768 := by
  have hu := unaligned_digit (lead := 0) (suffix := 96) (shift := 0) (width := 256) h
    (by omega) (by decide)
  have hX : X < 2^1024 := by
    have := h.1
    simpa [Limbs.radix, ← Nat.pow_mul] using this
  have hd : X / 2^768 < 2^256 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    simpa only [← Nat.pow_add] using hX
  have hw : (MachineState.readWord mem base).toNat < 2^256 := (MachineState.readWord mem base).val.isLt
  simp only [Nat.pow_zero, Nat.div_one, Nat.add_zero, Nat.add_zero] at hu
  rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hd] at hu
  simpa using hu

theorem top {mem : ByteArray} {base X : Nat} (h : Fast.Model.FastRepresents mem base 4 X) (k : Nat)
    (hk : k < 256) :
    (UInt256.shiftRight (MachineState.readWord mem base) (UInt256.ofNat k)).toNat = X / 2^(768 + k) := by
  rw [shiftRight_toNat _ hk, Nat.shiftRight_eq_div_pow, first_word h, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem low_shifted {mem : ByteArray} {base X : Nat} (h : Fast.Model.FastRepresents mem base 4 X) :
    (UInt256.land M (UInt256.shiftLeft (MachineState.readWord mem (base + 96)) (UInt256.ofNat 176))).toNat =
      X % 2^64 * 2^176 := by
  rw [land_M_toNat, HistoricalSearch.CRTWordBridge.shiftLeft_toNat _ 176 (by decide), Nat.shiftLeft_eq]
  have hu := unaligned_digit (lead := 96) (suffix := 0) (shift := 0) (width := 64) h (by omega) (by decide)
  simp only [Nat.pow_zero, Nat.div_one, Nat.add_zero, Nat.mul_zero] at hu
  -- (w * 2^176 mod 2^256) mod 2^240 = (w mod 2^64) * 2^176
  rw [Nat.mod_mod_of_dvd _ (by norm_num : (2:Nat)^240 ∣ 2^256)]
  rw [show (2:Nat)^240 = 2^64 * 2^176 by norm_num, Nat.mul_mod_mul_right, hu]

/-- The five digits of `X` (shift 0) recombine to `X`. -/
theorem value0 (X : Nat) :
    X % 2^240 + X / 2^240 % 2^240 * radix + X / 2^480 % 2^240 * radix^2 +
      X / 2^720 % 2^240 * radix^3 + X / 2^960 * radix^4 = X := by
  have h := CycleSubmission.InputWords.digit_decomposition radix X 4 (by norm_num [radix])
  simp only [weighted, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add] at h
  norm_num [radix, ← Nat.pow_mul, Nat.div_div_eq_div_mul, ← Nat.pow_add] at h ⊢
  omega

/-- The five digits of `X * 2^176` recombine to `X * 2^176`. -/
theorem value176 (X : Nat) :
    X % 2^64 * 2^176 + X / 2^64 % 2^240 * radix + X / 2^304 % 2^240 * radix^2 +
      X / 2^544 % 2^240 * radix^3 + X / 2^784 * radix^4 = X * 2^176 := by
  have h := CycleSubmission.InputWords.digit_decomposition radix (X * 2^176) 4 (by norm_num [radix])
  simp only [weighted, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add] at h
  have e0 : X * 2^176 / radix^0 % radix = X % 2^64 * 2^176 := by
    rw [pow_zero, Nat.div_one, show radix = 2^64 * 2^176 by norm_num [radix], Nat.mul_mod_mul_right]
  have e1 : X * 2^176 / radix^1 % radix = X / 2^64 % 2^240 := by
    rw [pow_one, show radix = 2^64 * 2^176 by norm_num [radix], Nat.mul_div_mul_right _ _ (by positivity)]
    norm_num
  have e2 : X * 2^176 / radix^2 % radix = X / 2^304 % 2^240 := by
    rw [show radix^2 = 2^304 * 2^176 by norm_num [radix], Nat.mul_div_mul_right _ _ (by positivity)]
    norm_num [radix]
  have e3 : X * 2^176 / radix^3 % radix = X / 2^544 % 2^240 := by
    rw [show radix^3 = 2^544 * 2^176 by norm_num [radix], Nat.mul_div_mul_right _ _ (by positivity)]
    norm_num [radix]
  have e4 : X * 2^176 / radix^4 = X / 2^784 := by
    rw [show radix^4 = 2^784 * 2^176 by norm_num [radix], Nat.mul_div_mul_right _ _ (by positivity)]
  rw [e0, e1, e2, e3, e4] at h
  linarith

end CycleSubmission.R5.Digits
