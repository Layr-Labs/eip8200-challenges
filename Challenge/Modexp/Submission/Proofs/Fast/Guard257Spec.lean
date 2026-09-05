import Challenge.Modexp.Submission.Proofs.Fast.Guard257Logic
import Challenge.Modexp.Submission.Proofs.Algorithm
import Mathlib.Tactic

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Spec

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open Guard257Data Guard257Logic

/-- The 257-bit public vector: base `2^256 + 5`, exponent `3`, modulus `2^256 + 7`. -/
def base : Nat := 2 ^ 256 + 5
def modulus : Nat := 2 ^ 256 + 7
/-- `(m - 2)^3 ≡ -8 (mod m)`, so the answer is `m - 8 = 2^256 - 1`. -/
def answer : Nat := 2 ^ 256 - 1

theorem certificate : Precompile.modPow base 3 modulus = answer := by
  rw [Algorithm.modPow_eq]
  norm_num [base, modulus, answer]

private theorem wordValue {input : ByteArray} (hm : Matches input)
    (off : Nat) (value : UInt256)
    (hmem : (off, value) ∈ checks) :
    Precompile.bytesToNatPadded input off 32 = value.toNat := by
  rw [← Challenge.EvmProof.Bytes.readWord_toNat, hm.2 _ hmem]

theorem sizes {input : ByteArray} (hm : Matches input) :
    baseSize input = 33 ∧ exponentSize input = 1 ∧ modulusSize input = 33 := by
  have h0 := wordValue hm 0 33 (by simp [checks])
  have h32 := wordValue hm 32 1 (by simp [checks])
  have h64 := wordValue hm 64 33 (by simp [checks])
  change Precompile.bytesToNatPadded input 0 32 = 33 at h0
  change Precompile.bytesToNatPadded input 32 32 = 1 at h32
  change Precompile.bytesToNatPadded input 64 32 = 33 at h64
  exact ⟨h0, h32, h64⟩

/-- Byte 128 (the last base byte) is `5`. -/
private theorem byte128 {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 128 1 = 5 := by
  have hw := wordValue hm 128
    2266871685857013885419158128209026732832114290800391293656575918782654971904
    (by simp [checks])
  change Precompile.bytesToNatPadded input 128 32 =
    2266871685857013885419158128209026732832114290800391293656575918782654971904 at hw
  rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 128 1 (by omega),
    Challenge.EvmProof.Bytes.readWord_toNat, hw]
  norm_num [Nat.shiftRight_eq_div_pow]

/-- Bytes 129 (exponent) and 130..159 (first 30 modulus bytes), from word 128. -/
private theorem tail128 {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 129 1 = 3 ∧
      Precompile.bytesToNatPadded input 130 30 =
        6901746346790563787434755862277025452451108972170386555162524223799296 := by
  have hw := wordValue hm 128
    2266871685857013885419158128209026732832114290800391293656575918782654971904
    (by simp [checks])
  change Precompile.bytesToNatPadded input 128 32 =
    2266871685857013885419158128209026732832114290800391293656575918782654971904 at hw
  have h5 := byte128 hm
  have hsplit1 := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 128 1 31
  have hsplit2 := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 129 1 30
  have hlt1 := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 129 1
  have hlt30 := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 130 30
  norm_num at hsplit1 hsplit2 hlt1 hlt30
  rw [hw, h5] at hsplit1
  rw [hsplit2] at hsplit1
  constructor <;> omega

theorem baseValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 96 33 = base := by
  have hw := wordValue hm 96
    452312848583266388373324160190187140051835877600158453279131187530910662656
    (by simp [checks])
  change Precompile.bytesToNatPadded input 96 32 =
    452312848583266388373324160190187140051835877600158453279131187530910662656 at hw
  have h5 := byte128 hm
  rw [show (33 : Nat) = 32 + 1 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  norm_num
  rw [hw, h5]
  norm_num [base]

theorem exponentValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 129 1 = 3 := (tail128 hm).1

theorem modulusValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 130 33 = modulus := by
  have hw := wordValue hm 160
    48312224427533946512043291035939178167157762805192705886137669566595072
    (by simp [checks])
  change Precompile.bytesToNatPadded input 160 32 =
    48312224427533946512043291035939178167157762805192705886137669566595072 at hw
  have hlast : Precompile.bytesToNatPadded input 160 3 = 7 := by
    rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 160 3 (by omega),
      Challenge.EvmProof.Bytes.readWord_toNat, hw]
    norm_num [Nat.shiftRight_eq_div_pow]
  have h30 := (tail128 hm).2
  rw [show (33 : Nat) = 30 + 3 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  norm_num
  rw [h30, hlast]
  norm_num [modulus]

set_option linter.unusedSimpArgs false in
theorem spec_eq {input : ByteArray} (hm : Matches input) :
    spec input = Precompile.natToBytes answer 33 := by
  rcases sizes hm with ⟨hbsize, hesize, hmsize⟩
  rw [spec, hbsize, hesize, hmsize]
  norm_num
  simp only [baseValue hm, exponentValue hm, modulusValue hm, certificate]

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Spec
