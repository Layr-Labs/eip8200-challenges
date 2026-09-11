import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
open Challenge.Ripemd160 EvmSemantics

def sizeFlag (input : ByteArray) : UInt256 :=
  UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.ofNat 56) (UInt256.ofNat input.size)) (UInt256.lor (UInt256.eq (UInt256.ofNat 120) (UInt256.ofNat input.size)) (UInt256.lor (UInt256.eq (UInt256.ofNat 63) (UInt256.ofNat input.size)) (UInt256.lor (UInt256.eq (UInt256.ofNat 64) (UInt256.ofNat input.size)) (UInt256.lor (UInt256.eq (UInt256.ofNat 65) (UInt256.ofNat input.size)) (UInt256.lor (UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat input.size)) (UInt256.lor (UInt256.eq (UInt256.ofNat 119) (UInt256.ofNat input.size)) (UInt256.lor (UInt256.eq (UInt256.ofNat 55) (UInt256.ofNat input.size)) (UInt256.lor (UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat input.size)) (UInt256.lor (UInt256.eq (UInt256.ofNat 31) (UInt256.ofNat input.size)) (UInt256.eq (UInt256.ofNat 32) (UInt256.ofNat input.size))))))))))))
theorem sizeFlag_hit (input : ByteArray)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32) : sizeFlag input = UInt256.ofNat 0 := by
  rcases hsize with h | h | h | h | h | h | h | h | h | h | h <;> unfold sizeFlag <;> rw [h] <;> decide

theorem sizeFlag_fail (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32) : sizeFlag input = UInt256.ofNat 1 := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have e56 := DirectGuard.size_eq_zero input 56 hlt (by norm_num) hsize.1
  have e120 := DirectGuard.size_eq_zero input 120 hlt (by norm_num) hsize.2.1
  have e63 := DirectGuard.size_eq_zero input 63 hlt (by norm_num) hsize.2.2.1
  have e64 := DirectGuard.size_eq_zero input 64 hlt (by norm_num) hsize.2.2.2.1
  have e65 := DirectGuard.size_eq_zero input 65 hlt (by norm_num) hsize.2.2.2.2.1
  have e128 := DirectGuard.size_eq_zero input 128 hlt (by norm_num) hsize.2.2.2.2.2.1
  have e119 := DirectGuard.size_eq_zero input 119 hlt (by norm_num) hsize.2.2.2.2.2.2.1
  have e55 := DirectGuard.size_eq_zero input 55 hlt (by norm_num) hsize.2.2.2.2.2.2.2.1
  have e1 := DirectGuard.size_eq_zero input 1 hlt (by norm_num) hsize.2.2.2.2.2.2.2.2.1
  have e31 := DirectGuard.size_eq_zero input 31 hlt (by norm_num) hsize.2.2.2.2.2.2.2.2.2.1
  have e32 := DirectGuard.size_eq_zero input 32 hlt (by norm_num) hsize.2.2.2.2.2.2.2.2.2.2
  unfold sizeFlag
  rw [e56, e120, e63, e64, e65, e128, e119, e55, e1, e31, e32]
  decide
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
