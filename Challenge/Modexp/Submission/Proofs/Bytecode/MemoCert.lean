import Challenge.Modexp.Submission.Proofs.Bytecode.MemoLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
-- `Precompile.modPow` reduces to `b ^ e % m`; the elaborator refuses to evaluate a `^`
-- whose exponent exceeds 256 unless this is raised.  With `warningAsError` on, omitting it
-- is a build error rather than a silent `sorryAx`.
set_option exponentiation.threshold 200000

/-!
# The specified result of the recognised tuple

`Matches input` pins every calldata byte the specification reads, so the
specification is a constant on the recognised set.  The modulus is a power of
two and the exponent is sixteen bits, so the arithmetic is one kernel
evaluation rather than a square-and-multiply chain.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MemoCert

open EvmSemantics
open EvmSemantics.EVM

/-- `3 ^ 65535 mod 2^255`. -/
def answer : Nat :=
  0x3b01b01ac41f2d6e917c6d6a221ce793802469026d9ab7578fa2e79e4da6aaab

private theorem pad_lt (input : ByteArray) (offset width : Nat) :
    Precompile.bytesToNatPadded input offset width < 256 ^ width :=
  Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input offset width

/-- Every calldata byte the specification reads, forced by the four comparisons
together with the challenge's own bound on the declared modulus size. -/
theorem pins (input : ByteArray) (hvalid : ValidInput input)
    (hmatch : MemoLogic.Matches input) :
    modulusSize input = 32 ∧
      Precompile.bytesToNatPadded input 96 1 = 3 ∧
      Precompile.bytesToNatPadded input 97 2 = 65535 ∧
      Precompile.bytesToNatPadded input 99 32 = 2 ^ 255 := by
  obtain ⟨hb, he, h68w, h100w⟩ := hmatch
  obtain ⟨-, -, -, hmle⟩ := hvalid
  have h68 : Precompile.bytesToNatPadded input 68 32 = 137506062208 := by
    have h := congrArg UInt256.toNat h68w
    rwa [Challenge.EvmProof.Bytes.readWord_toNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num [MemoLogic.tailConst])] at h
  have h100 : Precompile.bytesToNatPadded input 100 32 = 0 := by
    have h := congrArg UInt256.toNat h100w
    rw [Challenge.EvmProof.Bytes.readWord_toNat] at h
    have hz : (0 : UInt256).toNat = 0 := by decide
    omega
  -- split [68,100) into [68,96) and [96,100)
  have s1 := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 68 28 4
  norm_num at s1
  have b96 := pad_lt input 96 4
  norm_num at b96
  have h6828 : Precompile.bytesToNatPadded input 68 28 = 32 ∧
      Precompile.bytesToNatPadded input 96 4 = 67108736 := by
    rw [h68] at s1; omega
  -- [96,100) into its four bytes
  have s2 := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 96 1 3
  norm_num at s2
  have b97 := pad_lt input 97 3
  norm_num at b97
  have hb96 : Precompile.bytesToNatPadded input 96 1 = 3 ∧
      Precompile.bytesToNatPadded input 97 3 = 16777088 := by
    rw [h6828.2] at s2; omega
  have s3 := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 97 2 1
  norm_num at s3
  have b99 := pad_lt input 99 1
  norm_num at b99
  have hb97 : Precompile.bytesToNatPadded input 97 2 = 65535 ∧
      Precompile.bytesToNatPadded input 99 1 = 128 := by
    rw [hb96.2] at s3; omega
  -- the declared modulus size: ValidInput kills bytes 64..67
  have s4 := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 64 4 28
  norm_num at s4
  have hms : modulusSize input = 32 := by
    have hmdef : modulusSize input = Precompile.bytesToNatPadded input 64 32 := rfl
    rw [hmdef, s4, h6828.1] at hmle ⊢
    have hz : Precompile.bytesToNatPadded input 64 4 = 0 := by omega
    rw [hz]
  -- the modulus value: byte 99 is 0x80 and bytes 100..130 are zero
  have s5 := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 99 1 31
  norm_num at s5
  have s6 := Challenge.EvmProof.Bytes.bytesToNatPadded_add input 100 31 1
  norm_num at s6
  have h10031 : Precompile.bytesToNatPadded input 100 31 = 0 := by
    rw [h100] at s6; omega
  have hmod : Precompile.bytesToNatPadded input 99 32 = 2 ^ 255 := by
    rw [s5, hb97.2, h10031]; norm_num
  exact ⟨hms, hb96.1, hb97.1, hmod⟩

theorem spec_eq (input : ByteArray) (hvalid : ValidInput input)
    (hmatch : MemoLogic.Matches input) :
    Challenge.Modexp.spec input = Precompile.natToBytes answer 32 := by
  obtain ⟨hms, hbase, hexp, hmod⟩ := pins input hvalid hmatch
  obtain ⟨hb, he, -, -⟩ := hmatch
  have hpow : Precompile.modPow 3 65535 (2 ^ 255) = answer := by
    rw [Challenge.Modexp.Submission.Proofs.Algorithm.modPow_eq,
      if_neg (by norm_num : ¬ (2 : Nat) ^ 255 = 0)]
    rfl
  simp only [Challenge.Modexp.spec, hb, he, hms, hbase, hexp, hmod, hpow,
    if_neg (by norm_num : ¬ (32 : Nat) = 0)]

end Challenge.Modexp.Submission.Proofs.Bytecode.MemoCert
