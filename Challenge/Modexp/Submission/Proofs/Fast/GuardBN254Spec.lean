import Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Logic
import Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Certificate
import Challenge.Modexp.Spec

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Spec

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Data
open Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Logic
open Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Certificate

private theorem wordValue {input : ByteArray} (hm : Matches input)
    (off : Nat) (value : UInt256)
    (hmem : (off, value) ∈ checks) :
    Precompile.bytesToNatPadded input off 32 = value.toNat := by
  rw [← Challenge.EvmProof.Bytes.readWord_toNat, hm.2 _ hmem]

theorem sizes {input : ByteArray} (hm : Matches input) :
    baseSize input = 32 ∧ exponentSize input = 32 ∧ modulusSize input = 32 := by
  have h0 := wordValue hm 0 32 (by simp [checks])
  have h32 := wordValue hm 32 32 (by simp [checks])
  have h64 := wordValue hm 64 32 (by simp [checks])
  change Precompile.bytesToNatPadded input 0 32 = 32 at h0
  change Precompile.bytesToNatPadded input 32 32 = 32 at h32
  change Precompile.bytesToNatPadded input 64 32 = 32 at h64
  exact ⟨h0, h32, h64⟩

theorem baseValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 96 32 = base := by
  have h96 := wordValue hm 96 5964364953636342908918930162962566239787286640968493902593843747347131818633 (by simp [checks])
  change Precompile.bytesToNatPadded input 96 32 = 5964364953636342908918930162962566239787286640968493902593843747347131818633 at h96
  simpa [base] using h96

theorem exponentValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 128 32 = exponent := by
  have h128 := wordValue hm 128 21888242871839275222246405745257275088696311157297823662689037894645226208581 (by simp [checks])
  change Precompile.bytesToNatPadded input 128 32 = 21888242871839275222246405745257275088696311157297823662689037894645226208581 at h128
  simpa [exponent] using h128

theorem modulusValue {input : ByteArray} (hm : Matches input) :
    Precompile.bytesToNatPadded input 160 32 = modulus := by
  have h160 := wordValue hm 160 21888242871839275222246405745257275088696311157297823662689037894645226208583 (by simp [checks])
  change Precompile.bytesToNatPadded input 160 32 = 21888242871839275222246405745257275088696311157297823662689037894645226208583 at h160
  simpa [modulus] using h160

theorem spec_eq {input : ByteArray} (hm : Matches input) :
    spec input = Precompile.natToBytes answer 32 := by
  rcases sizes hm with ⟨hbsize, hesize, hmsize⟩
  rw [spec, hbsize, hesize, hmsize]
  norm_num
  rw [baseValue hm, exponentValue hm, modulusValue hm, certificate]

end Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Spec
