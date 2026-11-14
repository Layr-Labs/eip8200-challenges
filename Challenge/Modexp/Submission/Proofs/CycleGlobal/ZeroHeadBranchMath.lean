import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18378 - UInt256.ofNat 1938 * UInt256.ofNat 4 = UInt256.ofNat 10626 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18378 - UInt256.ofNat 1938 * UInt256.ofNat 8 = UInt256.ofNat 2874 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 10328 - UInt256.ofNat 11 * UInt256.ofNat 4 = UInt256.ofNat 10284 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 10328 - UInt256.ofNat 11 * UInt256.ofNat 8 = UInt256.ofNat 10240 := by decide
end CycleSubmission.Global.ZeroShiftMath
