import Challenge.EvmProof.Word
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadShiftDiet
open EvmSemantics Challenge.EvmProof.Word
private theorem shl_nat (x : UInt256) (n : Nat) (hn : n < 256) :
    (UInt256.shiftLeft x (UInt256.ofNat n)).toNat = (x.toNat * 2 ^ n) % 2 ^ 256 := by
  have hn' : n < 2 ^ 256 := by omega
  have hs : (UInt256.ofNat n).toNat = n := by
    rw [word_toNat_ofNat, Nat.mod_eq_of_lt hn']
  unfold UInt256.shiftLeft
  rw [hs, if_neg (by omega), word_toNat_ofNat]
  rw [Nat.shiftLeft_eq, UInt256.size, Nat.mod_mod]
private theorem mask_nat : (UInt256.ofNat (2 ^ 32 - 1)).toNat = 2 ^ 32 - 1 := by decide

theorem low (x : UInt256) :
    UInt256.shiftRight (UInt256.shiftLeft x (UInt256.ofNat 227)) (UInt256.ofNat 224) =
      UInt256.land (UInt256.shiftLeft x (UInt256.ofNat 3)) (UInt256.ofNat (2 ^ 32 - 1)) := by
  apply word_ext
  rw [shiftRight_toNat _ (by decide), shl_nat _ _ (by decide), word_toNat_land,
    shl_nat _ _ (by decide), mask_nat, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow]
  omega

theorem high (x : UInt256) :
    UInt256.shiftRight (UInt256.shiftLeft x (UInt256.ofNat 195)) (UInt256.ofNat 224) =
      UInt256.land (UInt256.shiftRight x (UInt256.ofNat 29)) (UInt256.ofNat (2 ^ 32 - 1)) := by
  apply word_ext
  rw [shiftRight_toNat _ (by decide), shl_nat _ _ (by decide), word_toNat_land,
    shiftRight_toNat _ (by decide), mask_nat, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow]
  omega
#print axioms low
#print axioms high
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadShiftDiet
