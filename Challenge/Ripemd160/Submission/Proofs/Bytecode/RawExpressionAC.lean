import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
open EvmSemantics PairedLaneUInt256Bridge
theorem add_comm (a b : UInt256) : UInt256.add a b = UInt256.add b a := by
  apply bits_injective
  simp only [bits_add]
  exact BitVec.add_comm _ _
theorem add_assoc (a b c : UInt256) : UInt256.add (UInt256.add a b) c = UInt256.add a (UInt256.add b c) := by
  apply bits_injective
  simp only [bits_add]
  exact BitVec.add_assoc _ _ _
theorem add_left_comm (a b c : UInt256) : UInt256.add a (UInt256.add b c) = UInt256.add b (UInt256.add a c) := by
  rw [← add_assoc, add_comm a b, add_assoc]
theorem mul_comm (a b : UInt256) : UInt256.mul a b = UInt256.mul b a := by
  apply bits_injective
  simp only [bits_mul]
  exact BitVec.mul_comm _ _
theorem mul_assoc (a b c : UInt256) : UInt256.mul (UInt256.mul a b) c = UInt256.mul a (UInt256.mul b c) := by
  apply bits_injective
  simp only [bits_mul]
  exact BitVec.mul_assoc _ _ _
theorem mul_left_comm (a b c : UInt256) : UInt256.mul a (UInt256.mul b c) = UInt256.mul b (UInt256.mul a c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]
theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply bits_injective
  simp only [bits_land]
  exact BitVec.and_comm _ _
theorem land_assoc (a b c : UInt256) : UInt256.land (UInt256.land a b) c = UInt256.land a (UInt256.land b c) := by
  apply bits_injective
  simp only [bits_land]
  exact BitVec.and_assoc _ _ _
theorem land_left_comm (a b c : UInt256) : UInt256.land a (UInt256.land b c) = UInt256.land b (UInt256.land a c) := by
  rw [← land_assoc, land_comm a b, land_assoc]
theorem lor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply bits_injective
  simp only [bits_lor]
  exact BitVec.or_comm _ _
theorem lor_assoc (a b c : UInt256) : UInt256.lor (UInt256.lor a b) c = UInt256.lor a (UInt256.lor b c) := by
  apply bits_injective
  simp only [bits_lor]
  exact BitVec.or_assoc _ _ _
theorem lor_left_comm (a b c : UInt256) : UInt256.lor a (UInt256.lor b c) = UInt256.lor b (UInt256.lor a c) := by
  rw [← lor_assoc, lor_comm a b, lor_assoc]
theorem xor_comm (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  apply bits_injective
  simp only [bits_xor]
  exact BitVec.xor_comm _ _
theorem xor_assoc (a b c : UInt256) : UInt256.xor (UInt256.xor a b) c = UInt256.xor a (UInt256.xor b c) := by
  apply bits_injective
  simp only [bits_xor]
  exact BitVec.xor_assoc _ _ _
theorem xor_left_comm (a b c : UInt256) : UInt256.xor a (UInt256.xor b c) = UInt256.xor b (UInt256.xor a c) := by
  rw [← xor_assoc, xor_comm a b, xor_assoc]
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
