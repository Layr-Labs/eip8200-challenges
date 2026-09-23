import Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianTrunc
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianTrunc16

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianLiteralBounds
open EvmSemantics Challenge.EvmProof
open DenseScheduleTemplate
open private and_mod_of_lt from Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianTrunc

theorem packedStage8_lt (value : UInt256) (hv : value.toNat < 2 ^ 160) :
    (packedStage value 8 mask8).toNat < 2 ^ 160 := by
  have hlow : (UInt256.land value mask8).toNat < 2 ^ 152 := by
    rw [Word.word_toNat_land, Nat.and_comm, ← and_mod_of_lt mask8.toNat value.toNat hv]
    apply Nat.lt_of_le_of_lt Nat.and_le_left
    decide
  have hleft : (UInt256.shiftLeft (UInt256.land value mask8) (UInt256.ofNat 8)).toNat < 2 ^ 160 := by
    unfold UInt256.shiftLeft
    rw [if_neg (by decide), Word.word_toNat_ofNat]
    norm_num only [Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    apply Nat.lt_of_le_of_lt (Nat.mod_le _ _)
    apply Nat.lt_of_le_of_lt (Nat.mod_le _ _)
    exact Nat.shiftLeft_lt hlow (m := 8)
  have hright : (UInt256.land (UInt256.shiftRight value (UInt256.ofNat 8)) mask8).toNat < 2 ^ 160 := by
    rw [Word.word_toNat_land]
    apply Nat.lt_of_le_of_lt Nat.and_le_left
    rw [Word.shiftRight_toNat value (by norm_num)]
    exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hv
  unfold packedStage
  rw [Word.word_toNat_lor]
  exact Nat.or_lt_two_pow hleft hright

#print axioms packedStage8_lt
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianLiteralBounds
