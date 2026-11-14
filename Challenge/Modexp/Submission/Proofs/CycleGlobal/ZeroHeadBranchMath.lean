import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18498 - UInt256.ofNat 1953 * UInt256.ofNat 4 = UInt256.ofNat 10686 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18498 - UInt256.ofNat 1953 * UInt256.ofNat 8 = UInt256.ofNat 2874 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 10388 - UInt256.ofNat 11 * UInt256.ofNat 4 = UInt256.ofNat 10344 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 10388 - UInt256.ofNat 11 * UInt256.ofNat 8 = UInt256.ofNat 10300 := by decide
end CycleSubmission.Global.ZeroShiftMath
