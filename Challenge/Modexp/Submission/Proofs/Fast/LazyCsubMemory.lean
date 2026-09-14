import Challenge.Modexp.Submission.Proofs.Fast.EarlyCsubModel

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.LazyCsub
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Csub

theorem sub_conditional_value (memory : ByteArray) (n tlow mm tn pdst : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (ht : Model.FastRepresents memory 2112 n tlow)
    (hm : Model.FastRepresents memory 0 n mm)
    (htnv : (MachineState.readWord memory 2080).toNat = tn) (htn1 : tn ≤ 1)
    (hbound : tn * Limbs.radix ^ n + tlow < Limbs.radix ^ n + mm) :
    Model.FastRepresents (subResultMemory memory n pdst) pdst n
      (if tn * Limbs.radix ^ n + tlow < mm then tn * Limbs.radix ^ n + tlow else tn * Limbs.radix ^ n + tlow - mm) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hinv, hbor⟩ := csStep_invariant memory n hn1 hn32 n le_rfl
  have hM : lowValue memory 0 n n = mm := by
    rw [lowValue_full]; exact Model.value_of_fastRepresents hm
  have hT : lowValue memory 2112 n n = tlow := by
    rw [lowValue_full]; exact Model.value_of_fastRepresents ht
  rw [hM, hT] at hinv
  have hDlt : lowValue (csStep memory n n).memory 1792 n n < Limbs.radix ^ n :=
    lowValue_lt _ _ _ _
  have hmmlt : mm < Limbs.radix ^ n := hm.1
  have htnStep : MachineState.readWord (csStep memory n n).memory 2080 =
      MachineState.readWord memory 2080 :=
    csStep_readWord_disjoint memory n 2080 hn1 (by omega) n le_rfl
  have htnStep' : (MachineState.readWord (csStep memory n n).memory 2080).toNat ≤ 1 := by
    rw [htnStep, htnv]; exact htn1
  have huseLe : (csUse memory n n).toNat ≤ 1 := csUse_le_one memory n n htnStep'
  have huse : (csUse memory n n).toNat =
      max tn (if (csStep memory n n).flag.toNat = 0 then 1 else 0) := by
    rw [csUse_toNat memory n n htnStep', htnStep, htnv]
  have hsubb : Model.FastRepresents (csStep memory n n).memory 1792 n
      (lowValue (csStep memory n n).memory 1792 n n) := fastRepresents_lowValue _ _ _
  have htsblk : Model.FastRepresents (csStep memory n n).memory 2112 n tlow :=
    fastRepresents_csStep memory n 2112 n tlow hn1 (by omega) ht n le_rfl
  by_cases huse0 : (csUse memory n n).toNat = 0
  · have huse0' : max tn (if (csStep memory n n).flag.toNat = 0 then 1 else 0) = 0 := by
      rw [← huse]; exact huse0
    have htn0 : tn = 0 := by omega
    have hbor1 : (csStep memory n n).flag.toNat = 1 := by
      by_contra hc
      have hb : (csStep memory n n).flag.toNat = 0 := by omega
      rw [hb, if_pos rfl] at huse0'
      omega
    rw [hbor1, Nat.one_mul] at hinv
    have hlt : tlow < mm := by omega
    have hmod : (if tn * Limbs.radix ^ n + tlow < mm then tn * Limbs.radix ^ n + tlow else tn * Limbs.radix ^ n + tlow - mm) = tlow := by
      rw [htn0, Nat.zero_mul, Nat.zero_add, if_pos hlt]
    rw [hmod]
    unfold subResultMemory
    rw [csSrc_toNat memory n n huseLe, if_pos huse0]
    exact fastRepresents_mcopy _ _ _ _ _ hn1 htsblk
  · have huse1' : max tn (if (csStep memory n n).flag.toNat = 0 then 1 else 0) = 1 := by
      rw [← huse]; omega
    have hcases : tn = 1 ∨ (csStep memory n n).flag.toNat = 0 := by
      by_cases hb : (csStep memory n n).flag.toNat = 0
      · exact Or.inr hb
      · rw [if_neg hb] at huse1'
        left; omega
    have hval : lowValue (csStep memory n n).memory 1792 n n + mm =
        tn * Limbs.radix ^ n + tlow := by
      rcases hcases with h1 | h0
      · rw [h1, Nat.one_mul] at hbound ⊢
        have hb1 : (csStep memory n n).flag.toNat = 1 := by
          by_contra hc
          have hb : (csStep memory n n).flag.toNat = 0 := by omega
          rw [hb, Nat.zero_mul, Nat.add_zero] at hinv
          omega
        rw [hb1, Nat.one_mul] at hinv
        omega
      · rw [h0, Nat.zero_mul, Nat.add_zero] at hinv
        have htn0 : tn = 0 := by
          by_contra hc
          have h1 : tn = 1 := by omega
          rw [h1, Nat.one_mul] at hbound
          omega
        rw [htn0, Nat.zero_mul, Nat.zero_add]
        omega
    have hmod : (if tn * Limbs.radix ^ n + tlow < mm then tn * Limbs.radix ^ n + tlow else tn * Limbs.radix ^ n + tlow - mm) =
        lowValue (csStep memory n n).memory 1792 n n := by
      rw [if_neg (by omega)]
      omega
    rw [hmod]
    unfold subResultMemory
    rw [csSrc_toNat memory n n huseLe, if_neg huse0]
    exact fastRepresents_mcopy _ _ _ _ _ hn1 hsubb

def resultMemory (memory : ByteArray) (n pdst : Nat) : ByteArray :=
  if (MachineState.readWord memory 2080).toNat = 0 then
    MachineState.writeBytes memory (MachineState.readPadded memory 2112 (32*n)) pdst
  else Csub.subResultMemory memory n pdst

def value (R mm u : Nat) : Nat := if R ≤ u then u - mm else u

theorem value_lt_radix {R mm u : Nat} (hmm : mm < R) (hu : u < R + mm) :
    value R mm u < R := by
  unfold value
  split <;> omega

theorem value_mod {R mm u : Nat} (hmm : mm < R) : value R mm u % mm = u % mm := by
  unfold value
  split
  · have hmu : mm ≤ u := by omega
    calc
      (u - mm) % mm = (u - mm + mm) % mm := (Nat.add_mod_right (u - mm) mm).symm
      _ = u % mm := by rw [Nat.sub_add_cancel hmu]
  · rfl

theorem result_represents (memory : ByteArray) (n tlow mm tn pdst : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (ht : Model.FastRepresents memory 2112 n tlow)
    (hm : Model.FastRepresents memory 0 n mm)
    (htnv : (MachineState.readWord memory 2080).toNat = tn) (htn1 : tn ≤ 1)
    (hbound : tn * Limbs.radix ^ n + tlow < Limbs.radix ^ n + mm) :
    Model.FastRepresents (resultMemory memory n pdst) pdst n
      (value (Limbs.radix ^ n) mm (tn * Limbs.radix ^ n + tlow)) := by
  unfold resultMemory
  rw [htnv]
  by_cases hz : tn = 0
  · rw [if_pos hz, hz, Nat.zero_mul, Nat.zero_add, value, if_neg (by have := ht.1; omega)]
    exact fastRepresents_mcopy memory 2112 pdst n tlow (by omega) ht
  · rw [if_neg hz]
    have hn1 : tn = 1 := by omega
    have hge : Limbs.radix ^ n ≤ tn * Limbs.radix ^ n + tlow := by
      rw [hn1, Nat.one_mul]
      omega
    have hnm : ¬ tn * Limbs.radix ^ n + tlow < mm := by have := hm.1; omega
    rw [value, if_pos hge]
    have hc := sub_conditional_value memory n tlow mm tn pdst hn hn32 ht hm htnv htn1 hbound
    rw [if_neg hnm] at hc
    exact hc

theorem result_preserves_region (memory : ByteArray) (n pdst ptr cnt v : Nat)
    (hn : 2 ≤ n)
    (hsub : ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr)
    (hdst : pdst + 32 * n ≤ ptr ∨ ptr + 32 * cnt ≤ pdst)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (resultMemory memory n pdst) ptr cnt v := by
  unfold resultMemory
  split
  · exact fastRepresents_mcopy_disjoint memory 2112 pdst (32*n) ptr cnt v hdst hrep
  · exact csub_sub_preserves_region memory n pdst ptr cnt v hn hsub hdst hrep

theorem result_readWord_outside (memory : ByteArray) (n pdst addr : Nat)
    (hn : 1 ≤ n) (hsub : addr+32 ≤ 1792 ∨ 1792+32*n ≤ addr)
    (hdst : addr+32 ≤ pdst ∨ pdst+32*n ≤ addr) :
    MachineState.readWord (resultMemory memory n pdst) addr = MachineState.readWord memory addr := by
  have hcopy (mem : ByteArray) (src : Nat) :
      MachineState.readWord (MachineState.writeBytes mem
        (MachineState.readPadded mem src (32*n)) pdst) addr = MachineState.readWord mem addr := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    rw [Challenge.EvmProof.Memory.readPadded_size]
    exact hdst
  unfold resultMemory
  split
  · exact hcopy memory 2112
  · unfold subResultMemory
    rw [hcopy]
    exact csStep_readWord_disjoint memory n addr hn hsub n le_rfl

end Challenge.Modexp.Submission.Proofs.Fast.LazyCsub
