import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18180 - UInt256.ofNat 1912 * UInt256.ofNat 4 = UInt256.ofNat 10532 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18180 - UInt256.ofNat 1912 * UInt256.ofNat 8 = UInt256.ofNat 2884 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 10214 - UInt256.ofNat 11 * UInt256.ofNat 4 = UInt256.ofNat 10170 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 10214 - UInt256.ofNat 11 * UInt256.ofNat 8 = UInt256.ofNat 10126 := by decide
end CycleSubmission.Global.ZeroShiftMath
