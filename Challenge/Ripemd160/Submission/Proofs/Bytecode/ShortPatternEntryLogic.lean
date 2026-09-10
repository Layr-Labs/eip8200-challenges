import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
open Challenge.Ripemd160 EvmSemantics

def sizeFlag (input : ByteArray) : UInt256 :=
  UInt256.isZero (UInt256.lor
    (UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat input.size))
    (UInt256.lor (UInt256.eq (UInt256.ofNat 120) (UInt256.ofNat input.size))
      (UInt256.eq (UInt256.ofNat 56) (UInt256.ofNat input.size))))

theorem sizeFlag_hit (input : ByteArray)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 128) :
    sizeFlag input = UInt256.ofNat 0 := by
  rcases hsize with h | h | h <;> unfold sizeFlag <;> rw [h] <;> decide

theorem sizeFlag_fail (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 128) :
    sizeFlag input = UInt256.ofNat 1 := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have e56 := DirectGuard.size_eq_zero input 56 hlt (by norm_num) hsize.1
  have e120 := DirectGuard.size_eq_zero input 120 hlt (by norm_num) hsize.2.1
  have e128 := DirectGuard.size_eq_zero input 128 hlt (by norm_num) hsize.2.2
  unfold sizeFlag
  rw [e56, e120, e128]
  decide
#print axioms sizeFlag_hit
#print axioms sizeFlag_fail
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
