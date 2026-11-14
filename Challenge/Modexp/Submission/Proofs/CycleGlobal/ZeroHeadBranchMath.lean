import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18362 - UInt256.ofNat 1936 * UInt256.ofNat 4 = UInt256.ofNat 10618 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18362 - UInt256.ofNat 1936 * UInt256.ofNat 8 = UInt256.ofNat 2874 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 10318 - UInt256.ofNat 11 * UInt256.ofNat 4 = UInt256.ofNat 10274 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 10318 - UInt256.ofNat 11 * UInt256.ofNat 8 = UInt256.ofNat 10230 := by decide
end CycleSubmission.Global.ZeroShiftMath
