import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18744 - UInt256.ofNat 2006 * UInt256.ofNat 4 = UInt256.ofNat 10720 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18744 - UInt256.ofNat 2006 * UInt256.ofNat 8 = UInt256.ofNat 2696 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 4075 - UInt256.ofNat 45 * UInt256.ofNat 4 = UInt256.ofNat 3895 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 4075 - UInt256.ofNat 45 * UInt256.ofNat 8 = UInt256.ofNat 3715 := by decide
end CycleSubmission.Global.ZeroShiftMath
