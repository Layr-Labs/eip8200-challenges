import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18602 - UInt256.ofNat 1966 * UInt256.ofNat 4 = UInt256.ofNat 10738 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18602 - UInt256.ofNat 1966 * UInt256.ofNat 8 = UInt256.ofNat 2874 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 10440 - UInt256.ofNat 11 * UInt256.ofNat 4 = UInt256.ofNat 10396 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 10440 - UInt256.ofNat 11 * UInt256.ofNat 8 = UInt256.ofNat 10352 := by decide
end CycleSubmission.Global.ZeroShiftMath
