import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxHeartbeats 1000000

/-!
# Mutually exclusive equality flags admit ADD instead of OR

This generic lemma is independent of the installed artifact. At the 256/376
size gate the equality flags cannot both be one, so their modular sum is their
bitwise OR. ADD and OR have the same static EVM charge, but their opcode bytes
can have different cost in the unchanged trusted literal renderer. The lemma
alone does not bind an alternate bytecode or prove whole-program correctness.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TwoLengthFlagAddition
open EvmSemantics Challenge.EvmProof

/-- The equality flags are disjoint for every 256-bit input, without a calldata
size bound. -/
theorem add_flags_eq_or (n : UInt256) :
    UInt256.add (UInt256.eq (UInt256.ofNat 376) n) (UInt256.eq (UInt256.ofNat 256) n) =
      UInt256.lor (UInt256.eq (UInt256.ofNat 376) n) (UInt256.eq (UInt256.ofNat 256) n) := by
  by_cases h256 : n.toNat = 256
  · have h376 : 376 ≠ n.toNat := by omega
    simp only [UInt256.eq, show (UInt256.ofNat 256).toNat = 256 by decide,
      show (UInt256.ofNat 376).toNat = 376 by decide,
      if_neg h376, if_pos h256.symm]
    decide
  · by_cases h376 : n.toNat = 376
    · have hn256 : 256 ≠ n.toNat := by omega
      simp only [UInt256.eq, show (UInt256.ofNat 256).toNat = 256 by decide,
        show (UInt256.ofNat 376).toNat = 376 by decide,
        if_neg hn256, if_pos h376.symm]
      decide
    · have hn256 : 256 ≠ n.toNat := Ne.symm h256
      have hn376 : 376 ≠ n.toNat := Ne.symm h376
      simp only [UInt256.eq, show (UInt256.ofNat 256).toNat = 256 by decide,
        show (UInt256.ofNat 376).toNat = 376 by decide,
        if_neg hn256, if_neg hn376]
      decide

#print axioms add_flags_eq_or
end Challenge.Ripemd160.Submission.Proofs.Bytecode.TwoLengthFlagAddition
