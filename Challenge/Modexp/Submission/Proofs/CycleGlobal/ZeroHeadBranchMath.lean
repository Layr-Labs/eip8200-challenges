import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18795 - UInt256.ofNat 2016 * UInt256.ofNat 4 = UInt256.ofNat 10731 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18795 - UInt256.ofNat 2016 * UInt256.ofNat 8 = UInt256.ofNat 2667 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 3940 - UInt256.ofNat 44 * UInt256.ofNat 4 = UInt256.ofNat 3764 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 3940 - UInt256.ofNat 44 * UInt256.ofNat 8 = UInt256.ofNat 3588 := by decide
end CycleSubmission.Global.ZeroShiftMath
