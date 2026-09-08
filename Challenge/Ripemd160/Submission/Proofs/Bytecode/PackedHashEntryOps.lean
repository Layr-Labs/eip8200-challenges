import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashEntry

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashEntryOps
open EvmSemantics Challenge.EvmProof

/-- Exact DUP/SHL64/OR arithmetic in each of the five hash-entry sites. -/
theorem duplicate_lane (x : UInt32) :
    (Word.ofUInt32 x |||
      UInt256.shiftLeft (Word.ofUInt32 x) (UInt256.ofNat 64)) =
        PackedHashEntry.packPair x x := by
  have hx := x.toNat_lt
  have h256 : x.toNat < 2 ^ 256 := by norm_num only [Nat.reducePow] at *; omega
  have h64 : x.toNat < 2 ^ 64 := by norm_num only [Nat.reducePow] at *; omega
  have hshift : x.toNat * 2 ^ 64 < 2 ^ 256 := by
    norm_num only [Nat.reducePow] at *
    omega
  unfold Word.ofUInt32
  rw [Word.shiftLeft_ofNat h256 (by norm_num) hshift]
  apply Word.word_ext
  change (UInt256.lor (UInt256.ofNat x.toNat)
    (UInt256.ofNat (x.toNat * 2 ^ 64))).toNat = _
  rw [Word.word_toNat_lor, PackedHashEntry.packPair_nat,
    Word.word_toNat_ofNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt h256, Nat.mod_eq_of_lt hshift]
  rw [Nat.or_comm, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_add_eq_or_of_lt h64]
  rw [Nat.shiftLeft_eq, Nat.add_comm]

#print axioms duplicate_lane
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashEntryOps
