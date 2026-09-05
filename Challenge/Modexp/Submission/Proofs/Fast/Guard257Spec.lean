import Challenge.Modexp.Submission.Proofs.Fast.Guard257Logic
import Challenge.Modexp.Submission.Proofs.Fast.RSA257Certificate
import Challenge.Modexp.Spec

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Spec

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Fast.Guard257Data
open Challenge.Modexp.Submission.Proofs.Fast.Guard257Logic
open Challenge.Modexp.Submission.Proofs.Fast.RSA257Certificate

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

theorem baseValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 96 33 = base := by
  have h96 := wordValue hm 96 452312848583266388373324160190187140051835877600158453279131187530910662656 (by simp [checks])
  have h128 := wordValue hm 128 2266871685857013885419158128209026732832114290800391293656575918782654971904 (by simp [checks])
  change Precompile.bytesToNatPadded input 96 32 = 452312848583266388373324160190187140051835877600158453279131187530910662656 at h96
  change Precompile.bytesToNatPadded input 128 32 = 2266871685857013885419158128209026732832114290800391293656575918782654971904 at h128
  have hsplit : Precompile.bytesToNatPadded input 96 33 =
      Precompile.bytesToNatPadded input 96 32 * 256 + Precompile.bytesToNatPadded input 128 1 := by
    have hs := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 96 32 1
    exact hs
  have hbyte128 : Precompile.bytesToNatPadded input 128 1 = 5 := by
    rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 128 1 (by omega),
      Challenge.EvmProof.Bytes.readWord_toNat, h128]
    decide
  rw [hsplit, h96, hbyte128]
  decide

theorem exponentValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 129 1 = 3 := by
  have h128 := wordValue hm 128 2266871685857013885419158128209026732832114290800391293656575918782654971904 (by simp [checks])
  change Precompile.bytesToNatPadded input 128 32 = 2266871685857013885419158128209026732832114290800391293656575918782654971904 at h128
  have hsplit : Precompile.bytesToNatPadded input 128 2 =
      Precompile.bytesToNatPadded input 128 1 * 256 + Precompile.bytesToNatPadded input 129 1 := by
    have hs := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 128 1 1
    exact hs
  have htwo : Precompile.bytesToNatPadded input 128 2 = 1283 := by
    rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 128 2 (by omega),
      Challenge.EvmProof.Bytes.readWord_toNat, h128]
    decide
  have hone : Precompile.bytesToNatPadded input 128 1 = 5 := by
    rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 128 1 (by omega),
      Challenge.EvmProof.Bytes.readWord_toNat, h128]
    decide
  omega

theorem modulusValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 130 33 = modulus := by
  have h128 := wordValue hm 128 2266871685857013885419158128209026732832114290800391293656575918782654971904 (by simp [checks])
  have h160 := wordValue hm 160 48312224427533946512043291035939178167157762805192705886137669566595072 (by simp [checks])
  change Precompile.bytesToNatPadded input 128 32 = 2266871685857013885419158128209026732832114290800391293656575918782654971904 at h128
  change Precompile.bytesToNatPadded input 160 32 = 48312224427533946512043291035939178167157762805192705886137669566595072 at h160
  have hthree : Precompile.bytesToNatPadded input 128 3 = 328449 := by
    rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 128 3 (by omega),
      Challenge.EvmProof.Bytes.readWord_toNat, h128]
    decide
  have htwo : Precompile.bytesToNatPadded input 128 2 = 1283 := by
    rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 128 2 (by omega),
      Challenge.EvmProof.Bytes.readWord_toNat, h128]
    decide
  have hsplit128_3 : Precompile.bytesToNatPadded input 128 3 =
      Precompile.bytesToNatPadded input 128 2 * 256 + Precompile.bytesToNatPadded input 130 1 := by
    have hs := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 128 2 1
    exact hs
  have h130 : Precompile.bytesToNatPadded input 130 1 = 1 := by omega
  have hsplit128_32 : Precompile.bytesToNatPadded input 128 32 =
      Precompile.bytesToNatPadded input 128 3 * 256^29 + Precompile.bytesToNatPadded input 131 29 := by
    have hs := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 128 3 29
    exact hs
  have hmid : Precompile.bytesToNatPadded input 131 29 = 0 := by
    rw [h128, hthree] at hsplit128_32
    omega
  have hlast : Precompile.bytesToNatPadded input 160 3 = 7 := by
    rw [← Challenge.EvmProof.Bytes.readWord_shift_toNat input 160 3 (by omega),
      Challenge.EvmProof.Bytes.readWord_toNat, h160]
    decide
  have hfull_split : Precompile.bytesToNatPadded input 130 33 =
      Precompile.bytesToNatPadded input 130 1 * 256^32 +
      Precompile.bytesToNatPadded input 131 29 * 256^3 +
      Precompile.bytesToNatPadded input 160 3 := by
    have hs1 := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 130 1 32
    have hs2 := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 131 29 3
    calc
      Precompile.bytesToNatPadded input 130 33 =
          Precompile.bytesToNatPadded input 130 1 * 256^32 + Precompile.bytesToNatPadded input 131 32 := hs1
      _ = Precompile.bytesToNatPadded input 130 1 * 256^32 +
          (Precompile.bytesToNatPadded input 131 29 * 256^3 + Precompile.bytesToNatPadded input 160 3) := by rw [hs2]
      _ = _ := by omega
  rw [hfull_split, h130, hmid, hlast]
  decide

theorem spec_eq {input : ByteArray} (hm : Matches input) :
    spec input = Precompile.natToBytes answer 33 := by
  rcases sizes hm with ⟨hbsize, hesize, hmsize⟩
  rw [spec, hbsize, hesize, hmsize]
  norm_num
  rw [baseValue hm, exponentValue hm, modulusValue hm, certificate]

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Spec
