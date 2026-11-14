import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18188 - UInt256.ofNat 1913 * UInt256.ofNat 4 = UInt256.ofNat 10536 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18188 - UInt256.ofNat 1913 * UInt256.ofNat 8 = UInt256.ofNat 2884 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 9912 - UInt256.ofNat 43 * UInt256.ofNat 4 = UInt256.ofNat 9740 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 9912 - UInt256.ofNat 43 * UInt256.ofNat 8 = UInt256.ofNat 9568 := by decide
end CycleSubmission.Global.ZeroShiftMath
