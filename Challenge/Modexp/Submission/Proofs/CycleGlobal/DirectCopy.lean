import Challenge.Modexp.Submission.Proofs.CycleGlobal.LazyTopMath
namespace CycleSubmission.Global.DirectCopy
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs Challenge.Modexp.Submission.Proofs.Fast
open Shift
def memory (mem : ByteArray) (n : Nat) : ByteArray := Exp.mcopyMem mem 256 2112 (32*n)
theorem readWord (mem : ByteArray) (n addr : Nat)
    (h : addr+32 ≤ 256 ∨ 256+32*n ≤ addr) :
    MachineState.readWord (memory mem n) addr = MachineState.readWord mem addr :=
  Exp.readWord_mcopyMem_disjoint _ _ _ _ _ h
theorem preserves (mem : ByteArray) (n ptr cnt value : Nat)
    (h : 256+32*n ≤ ptr ∨ ptr+32*cnt ≤ 256)
    (hr : Model.FastRepresents mem ptr cnt value) :
    Model.FastRepresents (memory mem n) ptr cnt value :=
  Exp.fastRepresents_mcopyMem_disjoint _ 256 2112 (32*n) ptr cnt value h hr
theorem copyValue (mem : ByteArray) (n value : Nat) (hn : 1 ≤ n)
    (hr : Model.FastRepresents mem 2112 n value) :
    Model.FastRepresents (memory mem n) 256 n value :=
  Exp.fastRepresents_mcopyMem _ 256 2112 n value hn hr
theorem invariant (mem : ByteArray) (n bsize mm minv : Nat) (hn8 : n ≤ 8)
    (inv : StepInv mem n bsize mm minv) : StepInv (memory mem n) n bsize mm minv where
  pre := by
    obtain ⟨p1,p2,p3,p4,p5⟩ := inv.pre
    have hz := readWord mem n 0 (Or.inl (by omega))
    refine ⟨?_,?_,?_,?_,?_⟩
    · rw [readWord mem n PRE_L (Or.inr (by simp only [PRE_L]; omega)),hz]; exact p1
    · rw [readWord mem n PRE_DODD (Or.inr (by simp only [PRE_DODD]; omega)),hz]; exact p2
    · rw [readWord mem n PRE_X (Or.inr (by simp only [PRE_X]; omega)),hz]; exact p3
    · rw [readWord mem n PRE_BMOD (Or.inr (by simp only [PRE_BMOD]; omega)),hz]; exact p4
    · rw [readWord mem n PRE_DINV (Or.inr (by simp only [PRE_DINV]; omega)),hz]; exact p5
  frame := {
    s32 := (readWord mem n 2688 (Or.inr (by omega))).trans inv.frame.s32
    minvW := (readWord mem n 2720 (Or.inr (by omega))).trans inv.frame.minvW
    ml := (readWord mem n 2752 (Or.inr (by omega))).trans inv.frame.ml
    tl := (readWord mem n 2784 (Or.inr (by omega))).trans inv.frame.tl
    eoff := (readWord mem n 2656 (Or.inr (by omega))).trans inv.frame.eoff }
  modulus := preserves mem n 0 n mm (Or.inr (by omega)) inv.modulus
  neg := preserves mem n NEG n _ (Or.inl (by unfold NEG; omega)) inv.neg
#print axioms invariant
end CycleSubmission.Global.DirectCopy
