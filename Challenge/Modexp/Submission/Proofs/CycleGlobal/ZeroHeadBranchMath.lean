import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 3124 - UInt256.shiftRight (UInt256.ofNat 4192) (UInt256.ofNat 4) = UInt256.ofNat 2862 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 3124 - UInt256.shiftRight (UInt256.ofNat 4192) (UInt256.ofNat 8) = UInt256.ofNat 3108 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 10574 + UInt256.shiftRight (UInt256.ofNat 736) (UInt256.ofNat 4) = UInt256.ofNat 10620 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 10574 + UInt256.shiftRight (UInt256.ofNat 736) (UInt256.ofNat 8) = UInt256.ofNat 10576 := by decide
end CycleSubmission.Global.ZeroShiftMath
