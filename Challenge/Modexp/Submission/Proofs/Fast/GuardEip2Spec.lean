import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Logic
import Challenge.Modexp.Submission.Proofs.Algorithm
import Challenge.Modexp.Spec

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Spec

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open GuardEip2Data GuardEip2Logic

def exponent : Nat := 115792089237316195423570985008687907853269984665640564039457584007908834671662
def modulus : Nat := 115792089237316195423570985008687907853269984665640564039457584007908834671663

theorem exponent_pos : 0 < exponent := by decide
theorem modulus_ne_zero : modulus ≠ 0 := by decide

theorem certificate : Precompile.modPow 0 exponent modulus = 0 :=
  Algorithm.modPow_zero_base exponent_pos modulus_ne_zero

private theorem wordValue {input : ByteArray} (hm : Matches input)
    (off : Nat) (value : UInt256)
    (hmem : (off, value) ∈ checks) :
    Precompile.bytesToNatPadded input off 32 = value.toNat := by
  rw [← Challenge.EvmProof.Bytes.readWord_toNat, hm.2 _ hmem]

theorem sizes {input : ByteArray} (hm : Matches input) :
    baseSize input = 0 ∧ exponentSize input = 32 ∧ modulusSize input = 32 := by
  have h0 := wordValue hm 0 0 (by simp [checks])
  have h32 := wordValue hm 32 32 (by simp [checks])
  have h64 := wordValue hm 64 32 (by simp [checks])
  change Precompile.bytesToNatPadded input 0 32 = 0 at h0
  change Precompile.bytesToNatPadded input 32 32 = 32 at h32
  change Precompile.bytesToNatPadded input 64 32 = 32 at h64
  exact ⟨h0, h32, h64⟩

theorem baseValue (input : ByteArray) :
    Precompile.bytesToNatPadded input 96 0 = 0 :=
  Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width input 96

theorem exponentValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 96 32 = exponent := by
  have hw := wordValue hm 96 115792089237316195423570985008687907853269984665640564039457584007908834671662 (by simp [checks])
  change Precompile.bytesToNatPadded input 96 32 = 115792089237316195423570985008687907853269984665640564039457584007908834671662 at hw
  exact hw

theorem modulusValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 128 32 = modulus := by
  have hw := wordValue hm 128 115792089237316195423570985008687907853269984665640564039457584007908834671663 (by simp [checks])
  change Precompile.bytesToNatPadded input 128 32 = 115792089237316195423570985008687907853269984665640564039457584007908834671663 at hw
  exact hw

set_option linter.unusedSimpArgs false in
theorem spec_eq {input : ByteArray} (hm : Matches input) :
    spec input = Precompile.natToBytes 0 32 := by
  rcases sizes hm with ⟨hbsize, hesize, hmsize⟩
  rw [spec, hbsize, hesize, hmsize]
  change
      Precompile.natToBytes
        (Precompile.modPow
          (Precompile.bytesToNatPadded input 96 0)
          (Precompile.bytesToNatPadded input 96 32)
          (Precompile.bytesToNatPadded input 128 32))
        32 =
      Precompile.natToBytes 0 32
  rw [baseValue, exponentValue hm, modulusValue hm, certificate]

end Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Spec
