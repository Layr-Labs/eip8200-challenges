import Challenge.Modexp.Submission.Proofs.Fast.Guard257Logic
import Challenge.Modexp.Submission.Proofs.Fast.RSA257Certificate

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Spec

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open Guard257Data Guard257Logic RSA257Certificate

private theorem wordValue {input : ByteArray} (hm : Matches input)
    (off : Nat) (value : UInt256) (hmem : (off, value) ∈ checks) :
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

private theorem word128 {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 128 32 =
      2266871685857013885419158128209026732832114290800391293656575918782654971904 := by
  have h := wordValue hm 128
    2266871685857013885419158128209026732832114290800391293656575918782654971904
    (by simp [checks])
  change Precompile.bytesToNatPadded input 128 32 =
    2266871685857013885419158128209026732832114290800391293656575918782654971904 at h
  exact h

private theorem prefix128 (input : ByteArray) (hm : Matches input) :
    Precompile.bytesToNatPadded input 128 2 = 1283 := by
  rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 128 2 (by omega),
    Challenge.EvmProof.Bytes.readWord_toNat, word128 hm]
  norm_num [Nat.shiftRight_eq_div_pow]

private theorem byte128 (input : ByteArray) (hm : Matches input) :
    Precompile.bytesToNatPadded input 128 1 = 5 := by
  rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 128 1 (by omega),
    Challenge.EvmProof.Bytes.readWord_toNat, word128 hm]
  norm_num [Nat.shiftRight_eq_div_pow]

theorem baseValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 96 33 = base := by
  have h96 := wordValue hm 96
    452312848583266388373324160190187140051835877600158453279131187530910662656
    (by simp [checks])
  change Precompile.bytesToNatPadded input 96 32 =
    452312848583266388373324160190187140051835877600158453279131187530910662656 at h96
  rw [show 33 = 32 + 1 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [h96, byte128 input hm]
  norm_num [base, radix]

theorem exponentValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 129 1 = 3 := by
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 128 1 1
  rw [prefix128 input hm, byte128 input hm] at hsplit
  norm_num at hsplit ⊢
  omega

theorem modulusValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 130 33 = modulus := by
  have hsplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 128 2 30
  rw [word128 hm, prefix128 input hm] at hsplit
  norm_num at hsplit
  have hfirst : Precompile.bytesToNatPadded input 130 30 = 2 ^ 232 := by
    omega
  have h160 := wordValue hm 160
    48312224427533946512043291035939178167157762805192705886137669566595072
    (by simp [checks])
  change Precompile.bytesToNatPadded input 160 32 =
    48312224427533946512043291035939178167157762805192705886137669566595072 at h160
  have hlast : Precompile.bytesToNatPadded input 160 3 = 7 := by
    rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 160 3 (by omega),
      Challenge.EvmProof.Bytes.readWord_toNat, h160]
    norm_num [Nat.shiftRight_eq_div_pow]
  rw [show 33 = 30 + 3 by omega,
    Challenge.EvmProof.Bytes.bytesToNatPadded_add]
  rw [hfirst, hlast]
  norm_num [modulus, radix]

theorem spec_eq {input : ByteArray} (hm : Matches input) :
    spec input = Precompile.natToBytes answer 33 := by
  rcases sizes hm with ⟨hbsize, hesize, hmsize⟩
  rw [spec, hbsize, hesize, hmsize]
  norm_num
  rw [baseValue hm, exponentValue hm, modulusValue hm, certificate]

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Spec
