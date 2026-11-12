import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18684 - UInt256.ofNat 1998 * UInt256.ofNat 4 = UInt256.ofNat 10692 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18684 - UInt256.ofNat 1998 * UInt256.ofNat 8 = UInt256.ofNat 2700 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 4039 - UInt256.ofNat 40 * UInt256.ofNat 4 = UInt256.ofNat 3879 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 4039 - UInt256.ofNat 40 * UInt256.ofNat 8 = UInt256.ofNat 3719 := by decide
end CycleSubmission.Global.ZeroShiftMath
