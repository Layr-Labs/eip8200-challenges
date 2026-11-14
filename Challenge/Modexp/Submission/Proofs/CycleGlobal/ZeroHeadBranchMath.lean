import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18490 - UInt256.ofNat 1952 * UInt256.ofNat 4 = UInt256.ofNat 10682 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18490 - UInt256.ofNat 1952 * UInt256.ofNat 8 = UInt256.ofNat 2874 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 10384 - UInt256.ofNat 11 * UInt256.ofNat 4 = UInt256.ofNat 10340 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 10384 - UInt256.ofNat 11 * UInt256.ofNat 8 = UInt256.ofNat 10296 := by decide
end CycleSubmission.Global.ZeroShiftMath
