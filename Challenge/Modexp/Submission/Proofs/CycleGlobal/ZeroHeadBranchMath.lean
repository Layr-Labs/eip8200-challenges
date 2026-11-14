import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18132 - UInt256.ofNat 1906 * UInt256.ofNat 4 = UInt256.ofNat 10508 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18132 - UInt256.ofNat 1906 * UInt256.ofNat 8 = UInt256.ofNat 2884 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 9884 - UInt256.ofNat 43 * UInt256.ofNat 4 = UInt256.ofNat 9712 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 9884 - UInt256.ofNat 43 * UInt256.ofNat 8 = UInt256.ofNat 9540 := by decide
end CycleSubmission.Global.ZeroShiftMath
