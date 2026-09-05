import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Logic
import Challenge.Modexp.Submission.Proofs.Algorithm

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Spec

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open GuardEip2Data GuardEip2Logic

/-- Compact form of the EIP-198 #2 exponent (`2^256 - 0x1000003d2`).
Kept irreducible so later `modPow` rewrites do not compute `2^256`. -/
@[irreducible] def exponent : Nat := 2 ^ 256 - 4294968274
/-- Compact form of the EIP-198 #2 modulus (`2^256 - 0x1000003d1`). -/
@[irreducible] def modulus : Nat := 2 ^ 256 - 4294968273

private theorem lt_two256 {k : Nat} (hk : k < 2 ^ 33) : k < 2 ^ 256 :=
  Nat.lt_trans hk (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 33 < 256))

theorem exponent_pos : 0 < exponent := by
  unfold exponent
  exact Nat.sub_pos_of_lt (lt_two256 (by decide : 4294968274 < 2 ^ 33))

theorem modulus_ne_zero : modulus ≠ 0 := by
  unfold modulus
  exact Nat.sub_ne_zero_of_lt (lt_two256 (by decide : 4294968273 < 2 ^ 33))

theorem certificate : Precompile.modPow 0 exponent modulus = 0 :=
  Algorithm.modPow_zero_base exponent_pos modulus_ne_zero

private theorem exponent_word :
    exponent =
      115792089237316195423570985008687907853269984665640564039457584007908834671662 := by
  unfold exponent
  native_decide

private theorem modulus_word :
    modulus =
      115792089237316195423570985008687907853269984665640564039457584007908834671663 := by
  unfold modulus
  native_decide

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
  have hw := wordValue hm 96
    115792089237316195423570985008687907853269984665640564039457584007908834671662
    (by simp [checks])
  change Precompile.bytesToNatPadded input 96 32 =
    115792089237316195423570985008687907853269984665640564039457584007908834671662 at hw
  rw [hw, exponent_word]

theorem modulusValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 128 32 = modulus := by
  have hw := wordValue hm 128
    115792089237316195423570985008687907853269984665640564039457584007908834671663
    (by simp [checks])
  change Precompile.bytesToNatPadded input 128 32 =
    115792089237316195423570985008687907853269984665640564039457584007908834671663 at hw
  rw [hw, modulus_word]

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
