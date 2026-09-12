import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Pad
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Pad
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
theorem paddedLength_aligned (n : Nat) (hn : n % 64 = 0) :
    Padding.paddedLength n = n + 64 := by
  unfold Padding.paddedLength
  omega

theorem zeroCount_aligned (n : Nat) (hn : n % 64 = 0) :
    Padding.zeroCount n = 55 := by
  rw [Padding.zeroCount, paddedLength_aligned n hn]
  omega

theorem padded_byte_aligned (input : ByteArray) (hn : input.size % 64 = 0)
    (j : Nat) (hj : j < 64) :
    (Padding.paddedMessage input)[input.size + j]?.getD 0 =
      if j = 0 then 128 else if j < 56 then 0 else
        (Padding.lengthBytes input)[j - 56]?.getD 0 := by
  have hz : Padding.zeroBytes input.size = ByteArray.mk (Array.replicate 55 0) := by
    rw [Padding.zeroBytes, zeroCount_aligned input.size hn]
  rw [Padding.paddedMessage, hz]
  simp only [Memory.getElem?_getD_append, ByteArray.size_append,
    show (ByteArray.mk #[0x80]).size = 1 by rfl,
    show (ByteArray.mk (Array.replicate 55 0)).size = 55 by rfl,
    Nat.add_assoc, Nat.add_lt_add_iff_left, Nat.add_sub_cancel_left]
  norm_num only
  by_cases h0 : j = 0
  · subst j
    simp
    rfl
  · by_cases h56 : j < 56
    · have hj1 : ¬ j < 1 := by omega
      simp only [if_pos h56, if_neg h0, if_neg hj1]
      rw [show input.size + j - (input.size + 1) = j - 1 by omega]
      change (Array.replicate 55 (0 : UInt8))[j - 1]?.getD 0 = 0
      rw [getElem?_pos _ _ (by simp only [Array.size_replicate]; omega)]
      simp
    · have hj1 : ¬ j < 1 := by omega
      simp only [if_neg h56, if_neg h0, if_neg hj1]
      congr 2
      omega

#print axioms padded_byte_aligned

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Pad
