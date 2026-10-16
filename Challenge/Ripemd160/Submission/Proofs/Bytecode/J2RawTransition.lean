import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2RawBase
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionRecurrence
private theorem hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem hsub_eq (a b : UInt256) : a - b = UInt256.sub a b := rfl

theorem repunit_div : UInt256.div c96 (UInt256.ofNat 96) = PatternedSwar.M := by decide

theorem repunit_hdiv : c96 / UInt256.ofNat 96 = PatternedSwar.M := by decide


/-- Reusing the shifted boundary sentinel gives the subtraction constant exactly. -/
theorem complement_sentinel_div9 :
    UInt256.div (UInt256.lnot (UInt256.shiftLeft c96 (UInt256.ofNat 2)))
      (UInt256.ofNat 9) = UInt256.mul (UInt256.ofNat 14) PatternedSwar.M := by decide

/-- The negative sentinel quotient is the additive inverse of the old subtraction constant. -/
theorem signed_sentinel_div9 :
    UInt256.sdiv (UInt256.shiftLeft c96 (UInt256.ofNat 2)) (UInt256.ofNat 9) =
      UInt256.sub (UInt256.ofNat 0) (UInt256.mul (UInt256.ofNat 14) PatternedSwar.M) := by decide

theorem add_negative_eq_sub (a b : UInt256) :
    UInt256.add a (UInt256.sub (UInt256.ofNat 0) b) = UInt256.sub a b := by
  unfold UInt256.add UInt256.sub
  congr 1
  simp [sub_eq_add_neg, UInt256.ofNat]

#print axioms signed_sentinel_div9
#print axioms add_negative_eq_sub
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
