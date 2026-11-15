import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.shiftLeft (UInt256.ofNat 33) (UInt256.ofNat 4) = UInt256.ofNat 528 := by decide
@[simp] theorem branch_normal8 : UInt256.shiftLeft (UInt256.ofNat 33) (UInt256.ofNat 8) = UInt256.ofNat 8448 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 10569 + UInt256.shiftRight (UInt256.ofNat 736) (UInt256.ofNat 4) = UInt256.ofNat 10615 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 10569 + UInt256.shiftRight (UInt256.ofNat 736) (UInt256.ofNat 8) = UInt256.ofNat 10571 := by decide
end CycleSubmission.Global.ZeroShiftMath
