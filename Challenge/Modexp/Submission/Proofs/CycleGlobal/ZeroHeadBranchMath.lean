import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftWords
namespace CycleSubmission.Global.ZeroShiftMath
open EvmSemantics
@[simp] theorem branch_normal4 : UInt256.ofNat 18692 - UInt256.ofNat 2000 * UInt256.ofNat 4 = UInt256.ofNat 10692 := by decide
@[simp] theorem branch_normal8 : UInt256.ofNat 18692 - UInt256.ofNat 2000 * UInt256.ofNat 8 = UInt256.ofNat 2692 := by decide
@[simp] theorem branch_zero4 : UInt256.ofNat 4047 - UInt256.ofNat 42 * UInt256.ofNat 4 = UInt256.ofNat 3879 := by decide
@[simp] theorem branch_zero8 : UInt256.ofNat 4047 - UInt256.ofNat 42 * UInt256.ofNat 8 = UInt256.ofNat 3711 := by decide
end CycleSubmission.Global.ZeroShiftMath
