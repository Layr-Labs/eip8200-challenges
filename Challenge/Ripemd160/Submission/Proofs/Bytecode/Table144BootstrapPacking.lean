import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Bootstrap
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Bootstrap
open EvmSemantics Challenge.EvmProof

theorem packed_ofUInt32_toNat (x : UInt32) :
    (packed (Word.ofUInt32 x)).toNat = x.toNat + x.toNat * 2^144 := by
  change (replication.toNat * (Word.ofUInt32 x).toNat) % 2^256 = _
  rw [Word.ofUInt32_toNat]
  have hrep : replication.toNat = 1 + 2^144 := by decide
  rw [hrep, Nat.mod_eq_of_lt (by have hx := x.toNat_lt; norm_num at hx ⊢; omega)]
  omega

theorem packed_ofUInt32 (x : UInt32) :
    packed (Word.ofUInt32 x) = UInt256.ofNat (x.toNat + x.toNat * 2^144) := by
  apply Word.word_ext
  rw [packed_ofUInt32_toNat, Word.word_toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by have hx := x.toNat_lt; norm_num at hx ⊢; omega)).symm

#print axioms packed_ofUInt32
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Bootstrap
