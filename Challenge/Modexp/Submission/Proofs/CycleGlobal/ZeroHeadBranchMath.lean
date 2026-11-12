import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18748 - UInt256.ofNat 2006 * UInt256.ofNat 4 = UInt256.ofNat 10724 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18748 - UInt256.ofNat 2006 * UInt256.ofNat 8 = UInt256.ofNat 2700 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 4079 - UInt256.ofNat 45 * UInt256.ofNat 4 = UInt256.ofNat 3899 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 4079 - UInt256.ofNat 45 * UInt256.ofNat 8 = UInt256.ofNat 3719 := by decide
end CycleSubmission.Global.ZeroShiftMath
