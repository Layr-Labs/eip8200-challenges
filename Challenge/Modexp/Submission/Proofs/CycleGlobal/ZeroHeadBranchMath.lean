import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18403 - UInt256.ofNat 1967 * UInt256.ofNat 4 = UInt256.ofNat 10535 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18403 - UInt256.ofNat 1967 * UInt256.ofNat 8 = UInt256.ofNat 2667 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 3932 - UInt256.ofNat 43 * UInt256.ofNat 4 = UInt256.ofNat 3760 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 3932 - UInt256.ofNat 43 * UInt256.ofNat 8 = UInt256.ofNat 3588 := by decide
end CycleSubmission.Global.ZeroShiftMath
