import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18712 - UInt256.ofNat 2004 * UInt256.ofNat 4 = UInt256.ofNat 10696 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18712 - UInt256.ofNat 2004 * UInt256.ofNat 8 = UInt256.ofNat 2680 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 4059 - UInt256.ofNat 45 * UInt256.ofNat 4 = UInt256.ofNat 3879 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 4059 - UInt256.ofNat 45 * UInt256.ofNat 8 = UInt256.ofNat 3699 := by decide
end CycleSubmission.Global.ZeroShiftMath
