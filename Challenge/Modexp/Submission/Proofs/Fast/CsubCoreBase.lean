import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreGasCs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
attribute [local simp] jumpDestCopyResume
-- Keep earlier limb states opaque while checking each explicit recursive step.
attribute [local irreducible] csStep

theorem fixedOrComm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  cases a with
  | mk a =>
    cases b with
    | mk b =>
      unfold UInt256.lor
      congr 1
      apply Fin.eq_of_val_eq
      simp [Fin.lor, Nat.or_comm]

theorem fixedSubtractZero (x : UInt256) : x - UInt256.ofNat 0 = x := by
  cases x with
  | mk x =>
    change (⟨x - 0⟩ : UInt256) = ⟨x⟩
    congr 1
    apply Fin.eq_of_val_eq
    simp

/-- Fixed-address CSUB boundary; the memory and borrow are the existing recursion. -/
def csFixedState (s : State) (memory : ByteArray) (n j pc : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := (if j = 0 then [] else [(csStep memory n j).flag]) ++ [pdst, ret] ++ rest
           memory := (csStep memory n j).memory }


end Challenge.Modexp.Submission.Proofs.Fast.Csub
