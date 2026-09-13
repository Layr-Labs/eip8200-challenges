import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144CommonFactorPlus
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarWide
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144WordRound

theorem low_rotate (a b : BitVec 32) (r : Nat) (hr0 : 0 < r) (hr : r < 32) :
    low ((pack a b * RootCommonFactorPlusProduct.coefficient) >>> (33-r)) = a.rotateLeft r := by
  exact RootCommonFactorPlusScalar.low_pack_rotate a b r hr0 hr

theorem bits_wordShift (x : UInt256) (n : Nat) (hn : n < 256) :
    bits (wordShift x n) = (bits x * RootCommonFactorPlusProduct.coefficient) >>> n := by
  rw [wordShift, bits_shr _ n hn, bits_mul]
  rfl
#print axioms low_rotate
#print axioms bits_wordShift
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalarWide
