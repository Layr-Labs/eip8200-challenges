import Challenge.Modexp.Submission.Proofs.Fast.CsubDispatch

set_option warningAsError true
set_option linter.unusedSimpArgs false
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

attribute [local irreducible] csStep

def amResultMemory (memory : ByteArray) (pa pb n : Nat) : ByteArray :=
  MachineState.writeBytes (amStep memory pa pb n n).memory
    (Data.Bytes.natToBytesPadded (amStep memory pa pb n n).flag.toNat 32) 8224

theorem amResultMemory_def (memory : ByteArray) (pa pb n : Nat) :
    amResultMemory memory pa pb n =
      MachineState.writeBytes (amStep memory pa pb n n).memory
        (Data.Bytes.natToBytesPadded (amStep memory pa pb n n).flag.toNat 32) 8224 := rfl

/-- The memory `CSUB` leaves behind. -/
def csResultMemory (memory : ByteArray) (n pdst : Nat) : ByteArray :=
  MachineState.writeBytes (csStep memory n n).memory
    (MachineState.readPadded (csStep memory n n).memory
      (csSrc memory n n).toNat (32 * n)) pdst

theorem csReturnedState_memory (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) :
    (csReturnedState s memory n n pdst ret rest).memory =
      csResultMemory memory n pdst.toNat := rfl

theorem addmod_carry_le_one (memory : ByteArray) (pa pb n : Nat) (hn : 2 ≤ n)
    (hpa : pa + 32 * n ≤ 8256) (hpb : pb + 32 * n ≤ 8256) :
    (amStep memory pa pb n n).flag.toNat ≤ 1 :=
  (amStep_invariant memory pa pb n (by omega) hpa hpb n le_rfl).2

/-- `ADDMOD` computes `a + b` as an `(n+1)`-limb value: the `t` block holds the
low `n` limbs and `TN` holds the carry. -/
theorem addmod_value (memory : ByteArray) (pa pb n a b : Nat) (hn : 2 ≤ n)
    (hpa : pa + 32 * n ≤ 8256) (hpb : pb + 32 * n ≤ 8256)
    (ha : Model.FastRepresents memory pa n a)
    (hb : Model.FastRepresents memory pb n b) :
    lowValue (amStep memory pa pb n n).memory 8256 n n +
        (amStep memory pa pb n n).flag.toNat * Limbs.radix ^ n = a + b := by
  have h := (amStep_invariant memory pa pb n (by omega) hpa hpb n le_rfl).1
  have hA : lowValue memory pa n n = a := by
    rw [lowValue_full]; exact Model.value_of_fastRepresents ha
  have hB : lowValue memory pb n n = b := by
    rw [lowValue_full]; exact Model.value_of_fastRepresents hb
  rw [hA, hB] at h
  exact h

theorem addmod_represents (memory : ByteArray) (pa pb n : Nat) :
    Model.FastRepresents (amResultMemory memory pa pb n) 8256 n
      (lowValue (amStep memory pa pb n n).memory 8256 n n) := by
  unfold amResultMemory
  exact Model.fastRepresents_writeWord_disjoint _ 8224 8256 n _ _ (by omega)
    (fastRepresents_lowValue _ _ _)

theorem addmod_tn (memory : ByteArray) (pa pb n : Nat) :
    MachineState.readWord (amResultMemory memory pa pb n) 8224 =
      (amStep memory pa pb n n).flag :=
  Challenge.EvmProof.Memory.readWord_writeWord _ _ _

/-- Every named block outside the `t` area survives `ADDMOD` unchanged. -/
theorem addmod_preserves_region (memory : ByteArray) (pa pb n ptr cnt v : Nat)
    (hn : 2 ≤ n)
    (hdisj : ptr + 32 * cnt ≤ 8224 ∨ 8256 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (amResultMemory memory pa pb n) ptr cnt v := by
  unfold amResultMemory
  exact Model.fastRepresents_writeWord_disjoint _ 8224 ptr cnt v _ (by omega)
    (fastRepresents_amStep memory pa pb n ptr cnt v (by omega) (by omega) hrep n le_rfl)

/-- `CSUB` writes `t mod m` into the block at `pd`. -/
theorem csub_correct (memory : ByteArray) (n tlow mm tn pdst : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (ht : Model.FastRepresents memory 8256 n tlow)
    (hm : Model.FastRepresents memory 0 n mm)
    (htnv : (MachineState.readWord memory 8224).toNat = tn) (htn1 : tn ≤ 1)
    (_hmpos : 0 < mm)
    (hbound : tn * Limbs.radix ^ n + tlow < 2 * mm) :
    Model.FastRepresents (csResultMemory memory n pdst) pdst n
      ((tn * Limbs.radix ^ n + tlow) % mm) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hinv, hbor⟩ := csStep_invariant memory n hn1 hn32 n le_rfl
  have hM : lowValue memory 0 n n = mm := by
    rw [lowValue_full]; exact Model.value_of_fastRepresents hm
  have hT : lowValue memory 8256 n n = tlow := by
    rw [lowValue_full]; exact Model.value_of_fastRepresents ht
  rw [hM, hT] at hinv
  have hDlt : lowValue (csStep memory n n).memory 7168 n n < Limbs.radix ^ n :=
    lowValue_lt _ _ _ _
  have hmmlt : mm < Limbs.radix ^ n := hm.1
  have htnStep : MachineState.readWord (csStep memory n n).memory 8224 =
      MachineState.readWord memory 8224 :=
    csStep_readWord_disjoint memory n 8224 hn1 (by omega) n le_rfl
  have htnStep' : (MachineState.readWord (csStep memory n n).memory 8224).toNat ≤ 1 := by
    rw [htnStep, htnv]; exact htn1
  have huseLe : (csUse memory n n).toNat ≤ 1 := csUse_le_one memory n n htnStep'
  have huse : (csUse memory n n).toNat =
      max tn (if (csStep memory n n).flag.toNat = 0 then 1 else 0) := by
    rw [csUse_toNat memory n n htnStep', htnStep, htnv]
  have hsubb : Model.FastRepresents (csStep memory n n).memory 7168 n
      (lowValue (csStep memory n n).memory 7168 n n) := fastRepresents_lowValue _ _ _
  have htsblk : Model.FastRepresents (csStep memory n n).memory 8256 n tlow :=
    fastRepresents_csStep memory n 8256 n tlow hn1 (by omega) ht n le_rfl
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
    have hmod : (tn * Limbs.radix ^ n + tlow) % mm = tlow := by
      rw [htn0, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hlt]
    rw [hmod]
    unfold csResultMemory
    rw [csSrc_toNat memory n n huseLe, if_pos huse0]
    exact fastRepresents_mcopy _ _ _ _ _ hn1 htsblk
  · have huse1' : max tn (if (csStep memory n n).flag.toNat = 0 then 1 else 0) = 1 := by
      rw [← huse]; omega
    have hcases : tn = 1 ∨ (csStep memory n n).flag.toNat = 0 := by
      by_cases hb : (csStep memory n n).flag.toNat = 0
      · exact Or.inr hb
      · rw [if_neg hb] at huse1'
        left; omega
    have hval : lowValue (csStep memory n n).memory 7168 n n + mm =
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
    have hmod : (tn * Limbs.radix ^ n + tlow) % mm =
        lowValue (csStep memory n n).memory 7168 n n := by
      rw [Model.mod_eq_cond_sub_of_lt_twice hbound, if_neg (by omega)]
      omega
    rw [hmod]
    unfold csResultMemory
    rw [csSrc_toNat memory n n huseLe, if_neg huse0]
    exact fastRepresents_mcopy _ _ _ _ _ hn1 hsubb

/-- Every block outside `SUBB` and outside the destination survives `CSUB`. -/
theorem csub_preserves_region (memory : ByteArray) (n pdst ptr cnt v : Nat)
    (hn : 2 ≤ n)
    (hdisjSubb : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hdisjDst : pdst + 32 * n ≤ ptr ∨ ptr + 32 * cnt ≤ pdst)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (csResultMemory memory n pdst) ptr cnt v := by
  unfold csResultMemory
  exact fastRepresents_mcopy_disjoint _ _ _ _ _ _ _ hdisjDst
    (fastRepresents_csStep memory n ptr cnt v (by omega) hdisjSubb hrep n le_rfl)

/-- End-to-end: entering `ADDMOD` with `a` at `pa`, `b` at `pb` and `a + b < 2m`
leaves `(a + b) mod m` in the block at `pd`. -/
theorem addmod_csub_correct (memory : ByteArray) (pa pb n a b mm pdst : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : pa + 32 * n ≤ 8192) (hpb : pb + 32 * n ≤ 8192)
    (ha : Model.FastRepresents memory pa n a)
    (hb : Model.FastRepresents memory pb n b)
    (hm : Model.FastRepresents memory 0 n mm) (hmpos : 0 < mm)
    (hab : a + b < 2 * mm) :
    Model.FastRepresents (csResultMemory (amResultMemory memory pa pb n) n pdst)
      pdst n ((a + b) % mm) := by
  have hcarry := addmod_carry_le_one memory pa pb n hn (by omega) (by omega)
  have hvalue := addmod_value memory pa pb n a b hn (by omega) (by omega) ha hb
  have hts := addmod_represents memory pa pb n
  have hmblk : Model.FastRepresents (amResultMemory memory pa pb n) 0 n mm :=
    addmod_preserves_region memory pa pb n 0 n mm hn (by omega) hm
  have htn : (MachineState.readWord (amResultMemory memory pa pb n) 8224).toNat =
      (amStep memory pa pb n n).flag.toNat := by
    rw [addmod_tn]
  have hbound : (amStep memory pa pb n n).flag.toNat * Limbs.radix ^ n +
      lowValue (amStep memory pa pb n n).memory 8256 n n < 2 * mm := by
    omega
  have h := csub_correct (amResultMemory memory pa pb n) n
    (lowValue (amStep memory pa pb n n).memory 8256 n n) mm
    (amStep memory pa pb n n).flag.toNat pdst hn hn32 hts hmblk htn hcarry hmpos hbound
  rwa [show (amStep memory pa pb n n).flag.toNat * Limbs.radix ^ n +
      lowValue (amStep memory pa pb n n).memory 8256 n n = a + b from by omega] at h

/-- Region preservation across the whole `ADDMOD`/`CSUB` pair. -/
theorem addmod_csub_preserves_region (memory : ByteArray) (pa pb n pdst ptr cnt v : Nat)
    (hn : 2 ≤ n)
    (hdisjT : ptr + 32 * cnt ≤ 8224 ∨ 8256 + 32 * n ≤ ptr)
    (hdisjSubb : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hdisjDst : pdst + 32 * n ≤ ptr ∨ ptr + 32 * cnt ≤ pdst)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (csResultMemory (amResultMemory memory pa pb n) n pdst)
      ptr cnt v :=
  csub_preserves_region _ n pdst ptr cnt v hn hdisjSubb hdisjDst
    (addmod_preserves_region memory pa pb n ptr cnt v hn hdisjT hrep)

end Challenge.Modexp.Submission.Proofs.Fast.Csub
