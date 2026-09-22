import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace5

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace RootE3Phase
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Shift

/-- The exact between-loop memory operations: clear phase, then copy the retained `TS` to ACC. -/
def phaseSwitch (mem : ByteArray) (n : Nat) : ByteArray :=
  Exp.mcopyMem (Exp.storeWord mem 1760 (UInt256.ofNat 0)) 256 2112 (32 * n)

theorem phaseSwitch_readWord (mem : ByteArray) (n addr : Nat)
    (hflag : addr + 32 ≤ 1760 ∨ 1792 ≤ addr)
    (hcopy : addr + 32 ≤ 256 ∨ 256 + 32 * n ≤ addr) :
    MachineState.readWord (phaseSwitch mem n) addr = MachineState.readWord mem addr := by
  unfold phaseSwitch
  rw [Exp.readWord_mcopyMem_disjoint _ _ _ _ _ hcopy]
  exact Csub.readWord_write_disjoint mem 0 addr 1760 hflag

theorem phaseSwitch_preserves (mem : ByteArray) (n ptr cnt value : Nat)
    (hflag : ptr + 32 * cnt ≤ 1760 ∨ 1792 ≤ ptr)
    (hcopy : 256 + 32 * n ≤ ptr ∨ ptr + 32 * cnt ≤ 256)
    (hrep : Model.FastRepresents mem ptr cnt value) :
    Model.FastRepresents (phaseSwitch mem n) ptr cnt value := by
  apply Exp.fastRepresents_mcopyMem_disjoint _ 256 2112 (32 * n) ptr cnt value hcopy
  exact Model.fastRepresents_writeWord_disjoint mem 1760 ptr cnt value 0 hflag.symm hrep

theorem phaseSwitch_copyY (mem : ByteArray) (n value : Nat) (hn : 1 ≤ n) (_hn8 : n ≤ 8)
    (hrep : Model.FastRepresents mem 2112 n value) :
    Model.FastRepresents (phaseSwitch mem n) 256 n value := by
  apply Exp.fastRepresents_mcopyMem _ 256 2112 n value hn
  exact Model.fastRepresents_writeWord_disjoint mem 1760 2112 n value 0
    (Or.inl (by omega)) hrep

theorem phaseSwitch_inv (mem : ByteArray) (n bsize mm minv : Nat) (hn8 : n ≤ 8)
    (inv : StepInv mem n bsize mm minv) :
    StepInv (phaseSwitch mem n) n bsize mm minv where
  pre := by
    obtain ⟨p1, p2, p3, p4, p5⟩ := inv.pre
    have hz := phaseSwitch_readWord mem n 0 (Or.inl (by omega)) (Or.inl (by omega))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [phaseSwitch_readWord mem n PRE_L (Or.inl (by simp only [PRE_L]; omega))
        (Or.inr (by simp only [PRE_L]; omega)), hz]; exact p1
    · rw [phaseSwitch_readWord mem n PRE_DODD (Or.inl (by simp only [PRE_DODD]; omega))
        (Or.inr (by simp only [PRE_DODD]; omega)), hz]; exact p2
    · rw [phaseSwitch_readWord mem n PRE_X (Or.inl (by simp only [PRE_X]; omega))
        (Or.inr (by simp only [PRE_X]; omega)), hz]; exact p3
    · rw [phaseSwitch_readWord mem n PRE_BMOD (Or.inl (by simp only [PRE_BMOD]; omega))
        (Or.inr (by simp only [PRE_BMOD]; omega)), hz]; exact p4
    · rw [phaseSwitch_readWord mem n PRE_DINV (Or.inl (by simp only [PRE_DINV]; omega))
        (Or.inr (by simp only [PRE_DINV]; omega)), hz]; exact p5
  frame := {
    s32 := (phaseSwitch_readWord mem n 2688 (Or.inr (by omega)) (Or.inr (by omega))).trans inv.frame.s32
    minvW := (phaseSwitch_readWord mem n 2720 (Or.inr (by omega)) (Or.inr (by omega))).trans inv.frame.minvW
    ml := (phaseSwitch_readWord mem n 2752 (Or.inr (by omega)) (Or.inr (by omega))).trans inv.frame.ml
    tl := (phaseSwitch_readWord mem n 2784 (Or.inr (by omega)) (Or.inr (by omega))).trans inv.frame.tl
    eoff := (phaseSwitch_readWord mem n 2816 (Or.inr (by omega)) (Or.inr (by omega))).trans inv.frame.eoff }
  modulus := phaseSwitch_preserves mem n 0 n mm (Or.inl (by omega)) (Or.inr (by omega)) inv.modulus
  neg := phaseSwitch_preserves mem n NEG n _ (Or.inl (by unfold NEG; omega))
    (Or.inl (by unfold NEG; omega)) inv.neg
  cache := (phaseSwitch_readWord mem n 1698 (Or.inl (by omega)) (Or.inr (by omega))).trans inv.cache

theorem represents_acc_after_steps (mem : ByteArray) (n mm value k : Nat)
    (hn : 1 ≤ n) (hn8 : n ≤ 8) (hrep : Model.FastRepresents mem 256 n value) :
    Model.FastRepresents (stepMems mem n mm k) 256 n value := by
  refine (Model.fastRepresents_congr (a := stepMems mem n mm k) (b := mem)
    (ptr := 256) (count := n) ?_ value).2 hrep
  intro i hi
  exact stepMems_readWord_disjoint mem n mm (256 + 32 * i) hn
    ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩ k

theorem two_phase_values (mem : ByteArray) (n bsize mm minv r k : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hm : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm) (inv : StepInv mem n bsize mm minv)
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) :
    let first := stepMems mem n mm (2 * k)
    let second := stepMems (phaseSwitch first n) n mm k
    Model.FastRepresents second 2112 n (r * Limbs.radix ^ (3 * k) % mm) ∧
      Model.FastRepresents second 256 n (r * Limbs.radix ^ (2 * k) % mm) := by
  dsimp only
  have invFirst := stepInv_stepMems (by omega) hn8 inv (2 * k)
  have firstBase := stepMems_represents mem n mm r hn hn8 hm hmm htop inv.modulus inv.neg
    hbase hr inv.pre (2 * k)
  have invBetween := phaseSwitch_inv _ n bsize mm minv hn8 invFirst
  have baseBetween := phaseSwitch_preserves _ n 2112 n _ (Or.inr (by omega))
    (Or.inl (by omega)) firstBase
  have hsecond := stepMems_represents _ n mm _ hn hn8 hm hmm htop invBetween.modulus
    invBetween.neg baseBetween (Nat.mod_lt _ hm) invBetween.pre k
  have hvalue : r * Limbs.radix ^ (2 * k) % mm * Limbs.radix ^ k % mm =
      r * Limbs.radix ^ (3 * k) % mm := by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add]
    rw [show 2 * k + k = 3 * k from by omega]
  rw [hvalue] at hsecond
  exact ⟨hsecond, represents_acc_after_steps _ n mm _ k (by omega) hn8
    (phaseSwitch_copyY _ n _ (by omega) hn8 firstBase)⟩

/-- Every entered shift path records its phase, including the ordinary path. -/
def flagSet (mem : ByteArray) (flag : UInt256) : ByteArray := Exp.storeWord mem 1760 flag

theorem flagSet_readWord (mem : ByteArray) (flag : UInt256) (addr : Nat)
    (h : addr + 32 ≤ 1760 ∨ 1792 ≤ addr) :
    MachineState.readWord (flagSet mem flag) addr = MachineState.readWord mem addr := by
  unfold flagSet Exp.storeWord
  exact Csub.readWord_write_disjoint mem flag.toNat addr 1760 h

theorem flagSet_preserves (mem : ByteArray) (flag : UInt256) (ptr cnt value : Nat)
    (h : ptr + 32 * cnt ≤ 1760 ∨ 1792 ≤ ptr)
    (hr : Model.FastRepresents mem ptr cnt value) :
    Model.FastRepresents (flagSet mem flag) ptr cnt value := by
  exact Model.fastRepresents_writeWord_disjoint mem 1760 ptr cnt value flag.toNat h.symm hr

theorem flagSet_inv (mem : ByteArray) (flag : UInt256) (n bsize mm minv : Nat)
    (hn8 : n ≤ 8) (inv : StepInv mem n bsize mm minv) :
    StepInv (flagSet mem flag) n bsize mm minv where
  pre := by
    obtain ⟨p1, p2, p3, p4, p5⟩ := inv.pre
    have hz := flagSet_readWord mem flag 0 (Or.inl (by omega))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [flagSet_readWord mem flag PRE_L (Or.inl (by simp only [PRE_L]; omega)), hz]; exact p1
    · rw [flagSet_readWord mem flag PRE_DODD (Or.inl (by simp only [PRE_DODD]; omega)), hz]
      exact p2
    · rw [flagSet_readWord mem flag PRE_X (Or.inl (by simp only [PRE_X]; omega)), hz]; exact p3
    · rw [flagSet_readWord mem flag PRE_BMOD (Or.inl (by simp only [PRE_BMOD]; omega)), hz]
      exact p4
    · rw [flagSet_readWord mem flag PRE_DINV (Or.inl (by simp only [PRE_DINV]; omega)), hz]
      exact p5
  frame := {
    s32 := (flagSet_readWord mem flag 2688 (Or.inr (by omega))).trans inv.frame.s32
    minvW := (flagSet_readWord mem flag 2720 (Or.inr (by omega))).trans inv.frame.minvW
    ml := (flagSet_readWord mem flag 2752 (Or.inr (by omega))).trans inv.frame.ml
    tl := (flagSet_readWord mem flag 2784 (Or.inr (by omega))).trans inv.frame.tl
    eoff := (flagSet_readWord mem flag 2816 (Or.inr (by omega))).trans inv.frame.eoff }
  modulus := flagSet_preserves mem flag 0 n mm (Or.inl (by omega)) inv.modulus
  neg := flagSet_preserves mem flag NEG n _ (Or.inl (by unfold NEG; omega)) inv.neg
  cache := (flagSet_readWord mem flag 1698 (Or.inl (by omega))).trans inv.cache

theorem flag_after_steps (mem : ByteArray) (flag : UInt256) (n mm k : Nat)
    (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    MachineState.readWord (stepMems (flagSet mem flag) n mm k) 1760 = flag := by
  rw [stepMems_readWord_disjoint _ n mm 1760 hn
    ⟨Or.inr (by omega), Or.inl (by omega), Or.inl (by omega)⟩ k]
  exact Challenge.EvmProof.Memory.readWord_writeWord mem 1760 flag

theorem inverse_not_zero (mm minv : Nat)
    (hinv : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) : minv ≠ 0 := by
  intro h
  subst minv
  norm_num at hinv

theorem inline_inverse_guard_iff (mm minv : Nat)
    (hinv : (mm % Limbs.radix * minv + 1) % 2 ^ 256 = 0) :
    1 < minv ↔ minv ≠ 1 := by
  have h := inverse_not_zero mm minv hinv
  omega

theorem width_guard_iff (n : Nat) (hn : 2 ≤ n) (hn8 : n ≤ 8) :
    UInt256.land (UInt256.ofNat n) (UInt256.ofNat 3) = UInt256.ofNat 0 ↔ n = 4 ∨ n = 8 := by
  have h : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

#print axioms flagSet_inv
#print axioms flag_after_steps
#print axioms inline_inverse_guard_iff
#print axioms width_guard_iff

def e3Prepared (mem input : ByteArray) (n : Nat) : ByteArray :=
  flagSet (m2Of mem input n) (UInt256.ofNat 1)

def e3Final (mem input : ByteArray) (n mm k : Nat) : ByteArray :=
  let first := stepMems (e3Prepared mem input n) n mm (2 * k)
  stepMems (phaseSwitch first n) n mm k


theorem m2_base_value (mem input : ByteArray) (n mm : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0) :
    Model.FastRepresents (m2Of mem input n) 2112 n
      (EvmSemantics.EVM.Precompile.bytesToNatPadded input 96 (32 * n) % mm) := by
  unfold m2Of preMem
  refine ShiftCacheModel.represents_cache _ n 2112 n _ (Or.inr (by omega)) ?_
  exact fastRepresents_preMemOf _ _ 2112 n _ (Or.inr (by unfold PRE_DINV; omega))
    (fastRepresents_negStep _ n 2112 n _ (Or.inr (by unfold NEG; omega))
      (m1_base mem input n mm hn hn8 hm hodd hmod htop htn0) n le_rfl)

theorem keep_one_steps (mem : ByteArray) (n mm value k : Nat)
    (hn : 1 ≤ n) (hn8 : n ≤ 8) (hr : Model.FastRepresents mem 768 n value) :
    Model.FastRepresents (stepMems mem n mm k) 768 n value := by
  refine (Model.fastRepresents_congr (a := stepMems mem n mm k) (b := mem)
    (ptr := 768) (count := n) ?_ value).2 hr
  intro i hi
  exact stepMems_readWord_disjoint mem n mm (768 + 32 * i) hn
    ⟨Or.inr (by omega), Or.inl (by omega), Or.inl (by omega)⟩ k
theorem e3_output_facts (mem input : ByteArray) (n bsize mm minv k : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hframe : Exp.Frame mem n bsize minv)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0)
    (hone : Model.FastRepresents mem 768 n 0) :
    let out := e3Final mem input n mm k
    let a := EvmSemantics.EVM.Precompile.bytesToNatPadded input 96 (32 * n) % mm
    Exp.Frame out n bsize minv ∧ Model.FastRepresents out 0 n mm ∧
      Model.FastRepresents out 2112 n (a * Limbs.radix ^ (3 * k) % mm) ∧
      Model.FastRepresents out 256 n (a * Limbs.radix ^ (2 * k) % mm) ∧
      Model.FastRepresents out 768 n 0 := by
  dsimp only
  have inv0 := m2_stepInv mem input n bsize mm minv hn hn8 hm hframe hmod
  have invPrep := flagSet_inv _ (UInt256.ofNat 1) n bsize mm minv hn8 inv0
  have hbase2 := m2_base_value mem input n mm hn hn8 hm hodd hmod htop htn0
  have hbasePrep := flagSet_preserves _ (UInt256.ofNat 1) 2112 n _ (Or.inr (by omega)) hbase2
  have htwo := R1.radix_pow_lt_two_mul (by omega) hodd hmod htop
  have vals := two_phase_values (e3Prepared mem input n) n bsize mm minv _ k hn hn8 hm
    (Model.fastRepresents_lt hmod) htwo invPrep hbasePrep (Nat.mod_lt _ hm)
  have invFirst := stepInv_stepMems (by omega) hn8 invPrep (2 * k)
  have invSwitch := phaseSwitch_inv _ n bsize mm minv hn8 invFirst
  have invFinal := stepInv_stepMems (by omega) hn8 invSwitch k
  have hone2 : Model.FastRepresents (m2Of mem input n) 768 n 0 := by
    refine (Model.fastRepresents_congr (a := m2Of mem input n) (b := mem)
      (ptr := 768) (count := n) ?_ 0).2 hone
    intro i hi
    exact m2_readWord_disjoint mem input n (768 + 32 * i) (by omega) hn8
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inl (by unfold NEG; omega),
       Or.inl (by unfold PRE_L; omega), Or.inl (by omega), Or.inl (by omega)⟩
  have honePrep := flagSet_preserves _ (UInt256.ofNat 1) 768 n 0 (Or.inl (by omega)) hone2
  have honeFirst := keep_one_steps _ n mm 0 (2 * k) (by omega) hn8 honePrep
  have honeSwitch := phaseSwitch_preserves _ n 768 n 0 (Or.inl (by omega))
    (Or.inl (by omega)) honeFirst
  have honeFinal := keep_one_steps _ n mm 0 k (by omega) hn8 honeSwitch
  exact ⟨invFinal.frame, invFinal.modulus, vals.1, vals.2, honeFinal⟩

#print axioms e3_output_facts



theorem m2_acc_value (mem input : ByteArray) (n mm : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0) :
    Model.FastRepresents (m2Of mem input n) 256 n
      (Precompile.bytesToNatPadded input 96 (32 * n) % mm) := by
  have h1 := m1_acc mem input n mm hn hn32 hm hodd hmod htop htn0
  unfold m2Of preMem
  refine ShiftCacheModel.represents_cache _ n 256 n _ (Or.inl (by omega)) ?_
  exact fastRepresents_preMemOf _ _ 256 n _ (Or.inl (by unfold PRE_L; omega))
    (fastRepresents_negStep _ n 256 n _ (Or.inl (by unfold NEG; omega)) h1 n le_rfl)

def ordinaryFinal (mem input : ByteArray) (n mm : Nat) : ByteArray :=
  stepMems (flagSet (m2Of mem input n) (UInt256.ofNat 0)) n mm n


theorem m2_one_value (mem input : ByteArray) (n : Nat) (hn : 1 ≤ n) (hn8 : n ≤ 8)
    (hone : Model.FastRepresents mem 768 n 0) :
    Model.FastRepresents (m2Of mem input n) 768 n 0 := by
  refine (Model.fastRepresents_congr (a := m2Of mem input n) (b := mem)
    (ptr := 768) (count := n) ?_ 0).2 hone
  intro i hi
  exact m2_readWord_disjoint mem input n (768 + 32 * i) hn hn8
    ⟨Or.inr (by omega), Or.inr (by omega), Or.inl (by unfold NEG; omega),
     Or.inl (by unfold PRE_L; omega), Or.inl (by omega), Or.inl (by omega)⟩

theorem ordinary_output_facts (mem input : ByteArray) (n bsize mm minv : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hframe : Exp.Frame mem n bsize minv)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0)
    (hone : Model.FastRepresents mem 768 n 0) :
    let out := ordinaryFinal mem input n mm
    let base := Precompile.bytesToNatPadded input 96 (32 * n)
    Exp.Frame out n bsize minv ∧ Model.FastRepresents out 0 n mm ∧
      Model.FastRepresents out 2112 n (base % mm * Limbs.radix ^ n % mm) ∧
      Model.FastRepresents out 256 n (base % mm) ∧
      Model.FastRepresents out 768 n 0 := by
  dsimp only
  have inv0 := m2_stepInv mem input n bsize mm minv hn hn8 hm hframe hmod
  have invPrep := flagSet_inv _ (UInt256.ofNat 0) n bsize mm minv hn8 inv0
  have invFinal := stepInv_stepMems (by omega) hn8 invPrep n
  have hbase2 := m2_base_value mem input n mm hn hn8 hm hodd hmod htop htn0
  have hbasePrep := flagSet_preserves _ (UInt256.ofNat 0) 2112 n _ (Or.inr (by omega)) hbase2
  have htwo := R1.radix_pow_lt_two_mul (by omega) hodd hmod htop
  have hbaseFinal := stepMems_represents (flagSet (m2Of mem input n) (UInt256.ofNat 0))
    n mm _ hn hn8 hm (Model.fastRepresents_lt hmod) htwo invPrep.modulus invPrep.neg
    hbasePrep (Nat.mod_lt _ hm) invPrep.pre n
  have hacc2 := m2_acc_value mem input n mm hn hn8 hm hodd hmod htop htn0
  have haccPrep := flagSet_preserves _ (UInt256.ofNat 0) 256 n _ (Or.inl (by omega)) hacc2
  have haccFinal := represents_acc_after_steps _ n mm _ n (by omega) hn8 haccPrep
  have hone2 := m2_one_value mem input n (by omega) hn8 hone
  have honePrep := flagSet_preserves _ (UInt256.ofNat 0) 768 n 0 (Or.inl (by omega)) hone2
  have honeFinal := keep_one_steps _ n mm 0 n (by omega) hn8 honePrep
  exact ⟨invFinal.frame, invFinal.modulus, hbaseFinal, haccFinal, honeFinal⟩

#print axioms m2_acc_value
#print axioms ordinary_output_facts
end RootE3Phase
