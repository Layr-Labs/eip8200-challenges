import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace4
import Challenge.Modexp.Submission.Proofs.CycleGlobal.LazyTopStep
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.LazyTopMath
open EvmSemantics
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Shift LazyTopStep
theorem stepMem_readWord_disjoint (mem : ByteArray) (n mm addr : Nat) (hn : 1 ≤ n)
    (hdisj : (addr + 32 ≤ 512 ∨ 512 + 32*n ≤ addr) ∧
      (addr + 32 ≤ 1792 ∨ 1792 + 32*n ≤ addr) ∧
      (addr + 32 ≤ 2080 ∨ 2112 + 32*n ≤ addr)) :
    MachineState.readWord (next mem n mm) addr = MachineState.readWord mem addr := by
  dsimp only [next]
  split
  · rw [mac_readWord_disjoint _ n addr _ hn (by omega)]
    exact uMem_readWord_disjoint mem n addr hdisj.2.2
  · exact Shift.stepMem_readWord_disjoint mem n mm addr hn hdisj
theorem fastRepresents_stepMem (mem : ByteArray) (n mm ptr cnt v : Nat) (hn : 1 ≤ n)
    (hdisj : (ptr + 32 * cnt ≤ 512 ∨ 512 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 2080 ∨ 2112 + 32 * n ≤ ptr))
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (next mem n mm) ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact stepMem_readWord_disjoint mem n mm _ hn (by omega)
open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Fast.QHat
theorem stepMems_modulus (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hmod : Model.FastRepresents mem 0 n mm) :
    ∀ k,Model.FastRepresents (iter mem n mm k) 0 n mm := by
  intro k
  induction k with
  | zero => exact hmod
  | succ k ih =>
      exact fastRepresents_stepMem _ n mm 0 n mm hn
        ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩ ih
theorem stepMems_neg (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm)) :
    ∀ k,Model.FastRepresents (iter mem n mm k) NEG n (Limbs.radix ^ n - mm) := by
  intro k
  induction k with
  | zero => exact hneg
  | succ k ih =>
      exact fastRepresents_stepMem _ n mm NEG n _ hn
        ⟨Or.inr (by unfold NEG; omega),Or.inl (by unfold NEG; omega),
          Or.inl (by unfold NEG; omega)⟩ ih
theorem PreOK_stepMem (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (h : PreOK mem) : PreOK (next mem n mm) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := h
  have hz : MachineState.readWord (next mem n mm) 0 = MachineState.readWord mem 0 :=
    stepMem_readWord_disjoint mem n mm 0 hn
      ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [stepMem_readWord_disjoint mem n mm PRE_L hn
      ⟨Or.inr (by simp only [PRE_L]; omega),Or.inl (by simp only [PRE_L]; omega),
        Or.inl (by simp only [PRE_L]; omega)⟩,hz]
    exact h1
  · rw [stepMem_readWord_disjoint mem n mm PRE_DODD hn
      ⟨Or.inr (by simp only [PRE_DODD]; omega),Or.inl (by simp only [PRE_DODD]; omega),
        Or.inl (by simp only [PRE_DODD]; omega)⟩,hz]
    exact h2
  · rw [stepMem_readWord_disjoint mem n mm PRE_X hn
      ⟨Or.inr (by simp only [PRE_X]; omega),Or.inl (by simp only [PRE_X]; omega),
        Or.inl (by simp only [PRE_X]; omega)⟩,hz]
    exact h3
  · rw [stepMem_readWord_disjoint mem n mm PRE_BMOD hn
      ⟨Or.inr (by simp only [PRE_BMOD]; omega),Or.inl (by simp only [PRE_BMOD]; omega),
        Or.inl (by simp only [PRE_BMOD]; omega)⟩,hz]
    exact h4
  · rw [stepMem_readWord_disjoint mem n mm PRE_DINV hn
      ⟨Or.inr (by simp only [PRE_DINV]; omega),Or.inl (by simp only [PRE_DINV]; omega),
        Or.inl (by simp only [PRE_DINV]; omega)⟩,hz]
    exact h5
theorem PreOK_stepMems (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (h : PreOK mem) : ∀ k,PreOK (iter mem n mm k) := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact PreOK_stepMem _ n mm hn hn32 ih
theorem stepMems_readWord_disjoint (mem : ByteArray) (n mm addr : Nat) (hn : 1 ≤ n)
    (hdisj : (addr + 32 ≤ 512 ∨ 512 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 2080 ∨ 2112 + 32 * n ≤ addr)) :
    ∀ k,MachineState.readWord (iter mem n mm k) addr = MachineState.readWord mem addr := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => exact (stepMem_readWord_disjoint _ n mm addr hn hdisj).trans ih
theorem stepMem_represents (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : PreOK mem) :
    Model.FastRepresents (next mem n mm) 2112 n (r * Limbs.radix % mm) := by
  have hrel := LazyTopStep.related_valid mem n mm r hn hn32 hmpos hmm htop hmod hneg hbase hr hpre
  have hold := Shift.stepMem_represents mem n mm r hn hn32 hmpos hmm htop hmod hneg hbase hr hpre
  refine (Model.fastRepresents_congr ?_ _).2 hold
  intro i hi
  exact TnCacheMemory.readWord_eq hrel.agree _ (Or.inr (by omega))
theorem stepMems_represents (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : PreOK mem) :
    ∀ k,Model.FastRepresents (iter mem n mm k) 2112 n (r * Limbs.radix ^ k % mm) := by
  intro k
  have hrel := LazyTopStep.iter_valid mem n mm r hn hn32 hmpos hmm htop hmod hneg hbase hr hpre k
  have hold := Shift.stepMems_represents mem n mm r hn hn32 hmpos hmm htop hmod hneg hbase hr hpre k
  refine (Model.fastRepresents_congr ?_ _).2 hold
  intro i hi
  exact TnCacheMemory.readWord_eq hrel.agree _ (Or.inr (by omega))
theorem frame_stepMem {mem : ByteArray} {n bsize mm minv : Nat} (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hf : Exp.Frame mem n bsize minv) : Exp.Frame (next mem n mm) n bsize minv where
  s32 := by
    rw [stepMem_readWord_disjoint mem n mm 2688 hn
      ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega)⟩]; exact hf.s32
  minvW := by
    rw [stepMem_readWord_disjoint mem n mm 2720 hn
      ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega)⟩]; exact hf.minvW
  ml := by
    rw [stepMem_readWord_disjoint mem n mm 2752 hn
      ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega)⟩]; exact hf.ml
  tl := by
    rw [stepMem_readWord_disjoint mem n mm 2784 hn
      ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega)⟩]; exact hf.tl
  eoff := by
    rw [stepMem_readWord_disjoint mem n mm 2656 hn
      ⟨Or.inr (by omega),Or.inr (by omega),Or.inr (by omega)⟩]; exact hf.eoff
theorem stepInv_stepMem {mem : ByteArray} {n bsize mm minv : Nat} (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (inv : StepInv mem n bsize mm minv) : StepInv (next mem n mm) n bsize mm minv where
  pre := PreOK_stepMem mem n mm hn hn32 inv.pre
  frame := frame_stepMem hn hn32 inv.frame
  modulus := fastRepresents_stepMem mem n mm 0 n mm hn
    ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩ inv.modulus
  neg := fastRepresents_stepMem mem n mm NEG n _ hn
    ⟨Or.inr (by unfold NEG; omega),Or.inl (by unfold NEG; omega),Or.inl (by unfold NEG; omega)⟩
    inv.neg
theorem stepInv_stepMems {mem : ByteArray} {n bsize mm minv : Nat} (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (inv : StepInv mem n bsize mm minv) :
    ∀ i,StepInv (iter mem n mm i) n bsize mm minv := by
  intro i
  induction i with
  | zero => exact inv
  | succ i ih => exact stepInv_stepMem hn hn32 ih
#print axioms stepMems_represents
end CycleSubmission.Global.LazyTopMath
