import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18482 - UInt256.ofNat 1951 * UInt256.ofNat 4 = UInt256.ofNat 10678 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18482 - UInt256.ofNat 1951 * UInt256.ofNat 8 = UInt256.ofNat 2874 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 10380 - UInt256.ofNat 11 * UInt256.ofNat 4 = UInt256.ofNat 10336 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 10380 - UInt256.ofNat 11 * UInt256.ofNat 8 = UInt256.ofNat 10292 := by decide
end CycleSubmission.Global.ZeroShiftMath
