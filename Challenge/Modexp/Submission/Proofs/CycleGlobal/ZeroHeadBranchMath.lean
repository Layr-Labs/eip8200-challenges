import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18410 - UInt256.ofNat 1942 * UInt256.ofNat 4 = UInt256.ofNat 10642 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18410 - UInt256.ofNat 1942 * UInt256.ofNat 8 = UInt256.ofNat 2874 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 10344 - UInt256.ofNat 11 * UInt256.ofNat 4 = UInt256.ofNat 10300 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 10344 - UInt256.ofNat 11 * UInt256.ofNat 8 = UInt256.ofNat 10256 := by decide
end CycleSubmission.Global.ZeroShiftMath
