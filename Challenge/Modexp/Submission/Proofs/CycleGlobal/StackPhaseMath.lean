import Challenge.Modexp.Submission.Proofs.CycleGlobal.DirectCopy
import Challenge.Modexp.Submission.Proofs.CycleGlobal.LazyTopMath
import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace5

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace CycleSubmission.Global.StackPhaseMath
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Shift

theorem represents_acc_after_steps (mem : ByteArray) (n mm value k : Nat)
    (hn : 1 ≤ n) (hn8 : n ≤ 8) (hrep : Model.FastRepresents mem 256 n value) :
    Model.FastRepresents (LazyTopStep.iter mem n mm k) 256 n value := by
  refine (Model.fastRepresents_congr (a := LazyTopStep.iter mem n mm k) (b := mem)
    (ptr := 256) (count := n) ?_ value).2 hrep
  intro i hi
  exact LazyTopMath.stepMems_readWord_disjoint mem n mm (256 + 32 * i) hn
    ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩ k

theorem two_phase_values (mem : ByteArray) (n bsize mm minv r k : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hm : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm) (inv : StepInv mem n bsize mm minv)
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) :
    let first := LazyTopStep.iter mem n mm (2 * k)
    let second := LazyTopStep.iter (CycleSubmission.Global.DirectCopy.memory first n) n mm k
    Model.FastRepresents second 2112 n (r * Limbs.radix ^ (3 * k) % mm) ∧
      Model.FastRepresents second 256 n (r * Limbs.radix ^ (2 * k) % mm) := by
  dsimp only
  have invFirst := LazyTopMath.stepInv_stepMems (by omega) hn8 inv (2 * k)
  have firstBase := LazyTopMath.stepMems_represents mem n mm r hn hn8 hm hmm htop inv.modulus inv.neg
    hbase hr inv.pre (2 * k)
  have invBetween := CycleSubmission.Global.DirectCopy.invariant _ n bsize mm minv hn8 invFirst
  have baseBetween := CycleSubmission.Global.DirectCopy.preserves _ n 2112 n _ 
    (Or.inl (by omega)) firstBase
  have hsecond := LazyTopMath.stepMems_represents _ n mm _ hn hn8 hm hmm htop invBetween.modulus
    invBetween.neg baseBetween (Nat.mod_lt _ hm) invBetween.pre k
  have hvalue : r * Limbs.radix ^ (2 * k) % mm * Limbs.radix ^ k % mm =
      r * Limbs.radix ^ (3 * k) % mm := by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add]
    rw [show 2 * k + k = 3 * k from by omega]
  rw [hvalue] at hsecond
  exact ⟨hsecond, represents_acc_after_steps _ n mm _ k (by omega) hn8
    (CycleSubmission.Global.DirectCopy.copyValue _ n _ (by omega)  firstBase)⟩

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


def e3Prepared (mem input : ByteArray) (n : Nat) : ByteArray :=
  (m2Of mem input n)

def e3Final (mem input : ByteArray) (n mm k : Nat) : ByteArray :=
  let first := LazyTopStep.iter (e3Prepared mem input n) n mm (2 * k)
  LazyTopStep.iter (CycleSubmission.Global.DirectCopy.memory first n) n mm k


theorem m2_base_value (mem input : ByteArray) (n mm : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0) :
    Model.FastRepresents (m2Of mem input n) 2112 n
      (EvmSemantics.EVM.Precompile.bytesToNatPadded input 96 (32 * n) % mm) := by
  unfold m2Of
  refine ShiftCacheModel.represents_cache _ n 2112 n _ (Or.inr (by omega)) ?_
  exact fastRepresents_preMem _ 2112 n _ (Or.inr (by unfold PRE_DINV; omega)) (by omega)
    (fastRepresents_negStep _ n 2112 n _ (Or.inr (by unfold NEG; omega))
      (m1_base mem input n mm hn hn8 hm hodd hmod htop htn0) n le_rfl)

theorem keep_one_steps (mem : ByteArray) (n mm value k : Nat)
    (hn : 1 ≤ n) (hn8 : n ≤ 8) (hr : Model.FastRepresents mem 768 n value) :
    Model.FastRepresents (LazyTopStep.iter mem n mm k) 768 n value := by
  refine (Model.fastRepresents_congr (a := LazyTopStep.iter mem n mm k) (b := mem)
    (ptr := 768) (count := n) ?_ value).2 hr
  intro i hi
  exact LazyTopMath.stepMems_readWord_disjoint mem n mm (768 + 32 * i) hn
    ⟨Or.inr (by omega), Or.inl (by omega), Or.inl (by omega)⟩ k
theorem e3_output_facts (mem input : ByteArray) (n bsize mm minv k : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hframe : Exp.Frame mem n bsize 0)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0)
    (hone : Model.FastRepresents mem 768 n 0)
    (hminvDef : minv = Setup.negWord (Setup.newton8 (mm % Limbs.radix))) :
    let out := e3Final mem input n mm k
    let a := EvmSemantics.EVM.Precompile.bytesToNatPadded input 96 (32 * n) % mm
    Exp.Frame out n bsize minv ∧ Model.FastRepresents out 0 n mm ∧
      Model.FastRepresents out 2112 n (a * Limbs.radix ^ (3 * k) % mm) ∧
      Model.FastRepresents out 256 n (a * Limbs.radix ^ (2 * k) % mm) ∧
      Model.FastRepresents out 768 n 0 := by
  dsimp only
  have inv0 := m2_stepInv mem input n bsize mm minv hn hn8 hm hodd hframe hmod hminvDef
  have invPrep := inv0
  have hbase2 := m2_base_value mem input n mm hn hn8 hm hodd hmod htop htn0
  have hbasePrep := hbase2
  have htwo := R1.radix_pow_lt_two_mul (by omega) hodd hmod htop
  have vals := two_phase_values (e3Prepared mem input n) n bsize mm minv _ k hn hn8 hm
    (Model.fastRepresents_lt hmod) htwo invPrep hbasePrep (Nat.mod_lt _ hm)
  have invFirst := LazyTopMath.stepInv_stepMems (by omega) hn8 invPrep (2 * k)
  have invSwitch := CycleSubmission.Global.DirectCopy.invariant _ n bsize mm minv hn8 invFirst
  have invFinal := LazyTopMath.stepInv_stepMems (by omega) hn8 invSwitch k
  have hone2 : Model.FastRepresents (m2Of mem input n) 768 n 0 := by
    refine (Model.fastRepresents_congr (a := m2Of mem input n) (b := mem)
      (ptr := 768) (count := n) ?_ 0).2 hone
    intro i hi
    exact m2_readWord_disjoint mem input n (768 + 32 * i) (by omega) hn8
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inl (by unfold NEG; omega),
       Or.inl (by unfold PRE_L; omega), Or.inl (by omega), Or.inl (by omega)⟩
      (Or.inl (by omega))
  have honePrep := hone2
  have honeFirst := keep_one_steps _ n mm 0 (2 * k) (by omega) hn8 honePrep
  have honeSwitch := CycleSubmission.Global.DirectCopy.preserves _ n 768 n 0 
    (Or.inl (by omega)) honeFirst
  have honeFinal := keep_one_steps _ n mm 0 k (by omega) hn8 honeSwitch
  exact ⟨invFinal.frame, invFinal.modulus, vals.1, vals.2, honeFinal⟩




theorem m2_acc_value (mem input : ByteArray) (n mm : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0) :
    Model.FastRepresents (m2Of mem input n) 256 n
      (Precompile.bytesToNatPadded input 96 (32 * n) % mm) := by
  have h1 := m1_acc mem input n mm hn hn32 hm hodd hmod htop htn0
  unfold m2Of
  refine ShiftCacheModel.represents_cache _ n 256 n _ (Or.inl (by omega)) ?_
  exact fastRepresents_preMem _ 256 n _ (Or.inl (by unfold PRE_L; omega)) (by omega)
    (fastRepresents_negStep _ n 256 n _ (Or.inl (by unfold NEG; omega)) h1 n le_rfl)

def ordinaryFinal (mem input : ByteArray) (n mm : Nat) : ByteArray :=
  LazyTopStep.iter ((m2Of mem input n)) n mm n


theorem m2_one_value (mem input : ByteArray) (n : Nat) (hn : 1 ≤ n) (hn8 : n ≤ 8)
    (hone : Model.FastRepresents mem 768 n 0) :
    Model.FastRepresents (m2Of mem input n) 768 n 0 := by
  refine (Model.fastRepresents_congr (a := m2Of mem input n) (b := mem)
    (ptr := 768) (count := n) ?_ 0).2 hone
  intro i hi
  exact m2_readWord_disjoint mem input n (768 + 32 * i) hn hn8
    ⟨Or.inr (by omega), Or.inr (by omega), Or.inl (by unfold NEG; omega),
     Or.inl (by unfold PRE_L; omega), Or.inl (by omega), Or.inl (by omega)⟩
    (Or.inl (by omega))

theorem ordinary_output_facts (mem input : ByteArray) (n bsize mm minv : Nat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hm : 0 < mm) (hodd : mm % 2 = 1)
    (hframe : Exp.Frame mem n bsize 0)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0)
    (hone : Model.FastRepresents mem 768 n 0)
    (hminvDef : minv = Setup.negWord (Setup.newton8 (mm % Limbs.radix))) :
    let out := ordinaryFinal mem input n mm
    let base := Precompile.bytesToNatPadded input 96 (32 * n)
    Exp.Frame out n bsize minv ∧ Model.FastRepresents out 0 n mm ∧
      Model.FastRepresents out 2112 n (base % mm * Limbs.radix ^ n % mm) ∧
      Model.FastRepresents out 256 n (base % mm) ∧
      Model.FastRepresents out 768 n 0 := by
  dsimp only
  have inv0 := m2_stepInv mem input n bsize mm minv hn hn8 hm hodd hframe hmod hminvDef
  have invPrep := inv0
  have invFinal := LazyTopMath.stepInv_stepMems (by omega) hn8 invPrep n
  have hbase2 := m2_base_value mem input n mm hn hn8 hm hodd hmod htop htn0
  have hbasePrep := hbase2
  have htwo := R1.radix_pow_lt_two_mul (by omega) hodd hmod htop
  have hbaseFinal := LazyTopMath.stepMems_represents ((m2Of mem input n))
    n mm _ hn hn8 hm (Model.fastRepresents_lt hmod) htwo invPrep.modulus invPrep.neg
    hbasePrep (Nat.mod_lt _ hm) invPrep.pre n
  have hacc2 := m2_acc_value mem input n mm hn hn8 hm hodd hmod htop htn0
  have haccPrep := hacc2
  have haccFinal := represents_acc_after_steps _ n mm _ n (by omega) hn8 haccPrep
  have hone2 := m2_one_value mem input n (by omega) hn8 hone
  have honePrep := hone2
  have honeFinal := keep_one_steps _ n mm 0 n (by omega) hn8 honePrep
  exact ⟨invFinal.frame, invFinal.modulus, hbaseFinal, haccFinal, honeFinal⟩

end CycleSubmission.Global.StackPhaseMath

