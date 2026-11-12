import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18783 - UInt256.ofNat 2011 * UInt256.ofNat 4 = UInt256.ofNat 10739 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18783 - UInt256.ofNat 2011 * UInt256.ofNat 8 = UInt256.ofNat 2695 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 4092 - UInt256.ofNat 44 * UInt256.ofNat 4 = UInt256.ofNat 3916 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 4092 - UInt256.ofNat 44 * UInt256.ofNat 8 = UInt256.ofNat 3740 := by decide
end CycleSubmission.Global.ZeroShiftMath
