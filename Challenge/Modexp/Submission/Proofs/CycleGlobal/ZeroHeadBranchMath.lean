import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18566 - UInt256.ofNat 1963 * UInt256.ofNat 4 = UInt256.ofNat 10714 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18566 - UInt256.ofNat 1963 * UInt256.ofNat 8 = UInt256.ofNat 2862 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 10418 - UInt256.ofNat 11 * UInt256.ofNat 4 = UInt256.ofNat 10374 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 10418 - UInt256.ofNat 11 * UInt256.ofNat 8 = UInt256.ofNat 10330 := by decide
end CycleSubmission.Global.ZeroShiftMath
