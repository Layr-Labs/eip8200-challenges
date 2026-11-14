import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18402 - UInt256.ofNat 1941 * UInt256.ofNat 4 = UInt256.ofNat 10638 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18402 - UInt256.ofNat 1941 * UInt256.ofNat 8 = UInt256.ofNat 2874 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 10340 - UInt256.ofNat 11 * UInt256.ofNat 4 = UInt256.ofNat 10296 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 10340 - UInt256.ofNat 11 * UInt256.ofNat 8 = UInt256.ofNat 10252 := by decide
end CycleSubmission.Global.ZeroShiftMath
