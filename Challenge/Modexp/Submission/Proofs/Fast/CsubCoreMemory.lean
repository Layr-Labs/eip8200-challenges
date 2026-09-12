import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreArithmeticCs
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
/-! ## Region preservation -/

theorem fastRepresents_amStep (memory : ByteArray) (pa pb n ptr cnt v : Nat)
    (hn : 1 ≤ n)
    (hdisj : ptr + 32 * cnt ≤ 2112 ∨ 2112 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents memory ptr cnt v) (j : Nat) (hj : j ≤ n) :
    Model.FastRepresents (amStep memory pa pb n j).memory ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact amStep_readWord_disjoint memory pa pb n _ hn (by omega) j hj

theorem fastRepresents_csStep (memory : ByteArray) (n ptr cnt v : Nat)
    (hn : 1 ≤ n)
    (hdisj : ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents memory ptr cnt v) (j : Nat) (hj : j ≤ n) :
    Model.FastRepresents (csStep memory n j).memory ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact csStep_readWord_disjoint memory n _ hn (by omega) j hj

/-! ## `MCOPY` -/

theorem readPadded_mcopy (memory : ByteArray) (src dst sz i : Nat)
    (h : 32 * i + 32 ≤ sz) :
    MachineState.readPadded (MachineState.writeBytes memory
        (MachineState.readPadded memory src sz) dst) (dst + 32 * i) 32 =
      MachineState.readPadded memory (src + 32 * i) 32 := by
  apply ByteArray.ext_getElem
  · simp
  · intro k hk1 hk2
    have hk : k < 32 := by simpa using hk1
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk1,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hk2,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hk, if_pos hk,
      MachineState.writeBytes_getElem?_getD,
      Challenge.EvmProof.Memory.readPadded_size,
      if_pos (show dst ≤ dst + 32 * i + k ∧ dst + 32 * i + k < dst + sz from
        ⟨by omega, by omega⟩),
      show dst + 32 * i + k - dst = 32 * i + k from by omega,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos (show 32 * i + k < sz from by omega)]
    simp only [Nat.add_assoc]

theorem readWord_mcopy (memory : ByteArray) (src dst sz i : Nat)
    (h : 32 * i + 32 ≤ sz) :
    MachineState.readWord (MachineState.writeBytes memory
        (MachineState.readPadded memory src sz) dst) (dst + 32 * i) =
      MachineState.readWord memory (src + 32 * i) := by
  unfold MachineState.readWord
  rw [readPadded_mcopy memory src dst sz i h]

/-- The `MCOPY` reproduces the source block at the destination. -/
theorem fastRepresents_mcopy (memory : ByteArray) (src dst n v : Nat) (_hn : 1 ≤ n)
    (hrep : Model.FastRepresents memory src n v) :
    Model.FastRepresents (MachineState.writeBytes memory
      (MachineState.readPadded memory src (32 * n)) dst) dst n v := by
  apply Model.fastRepresents_of_limbs hrep.1
  intro k hk
  rw [readWord_mcopy memory src dst (32 * n) (n - 1 - k) (by omega)]
  exact Model.readLimb_of_fastRepresents hrep hk

/-- The `MCOPY` leaves every block outside the destination alone. -/
theorem fastRepresents_mcopy_disjoint (memory : ByteArray) (src dst sz ptr cnt v : Nat)
    (hdisj : dst + sz ≤ ptr ∨ ptr + 32 * cnt ≤ dst)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (MachineState.writeBytes memory
      (MachineState.readPadded memory src sz) dst) ptr cnt v := by
  apply Model.fastRepresents_writeBytes_disjoint
  · rw [Challenge.EvmProof.Memory.readPadded_size]
    exact hdisj
  · exact hrep

/-! ## The selection word -/

theorem word_toNat_mul (a b : UInt256) :
    (a * b).toNat = a.toNat * b.toNat % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

theorem csUse_le_one (memory : ByteArray) (n j : Nat)
    (htn : (MachineState.readWord (csStep memory n j).memory 2080).toNat ≤ 1) :
    (csUse memory n j).toNat ≤ 1 := by
  rw [csUse, Challenge.EvmProof.Word.word_toNat_lor]
  have hz : (UInt256.isZero (csStep memory n j).flag).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_isZero]
    split <;> omega
  rw [or_of_le_one htn hz]
  omega

theorem csUse_toNat (memory : ByteArray) (n j : Nat)
    (htn : (MachineState.readWord (csStep memory n j).memory 2080).toNat ≤ 1) :
    (csUse memory n j).toNat =
      max (MachineState.readWord (csStep memory n j).memory 2080).toNat
        (if (csStep memory n j).flag.toNat = 0 then 1 else 0) := by
  have hz : (UInt256.isZero (csStep memory n j).flag).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_isZero]
    split <;> omega
  rw [csUse, Challenge.EvmProof.Word.word_toNat_lor, or_of_le_one htn hz,
    Challenge.EvmProof.Word.word_toNat_isZero]

theorem csSrc_toNat (memory : ByteArray) (n j : Nat)
    (huse : (csUse memory n j).toNat ≤ 1) :
    (csSrc memory n j).toNat =
      if (csUse memory n j).toNat = 0 then 2112 else 1792 := by
  have h8256 : (2112 : UInt256).toNat = 2112 := by decide
  have hL : (115792089237316195423570985008687907853269984665640564039457584007913129639616 :
      UInt256).toNat =
      115792089237316195423570985008687907853269984665640564039457584007913129639616 := by
    decide
  rw [csSrc, Challenge.EvmProof.Word.word_toNat_add, word_toNat_mul, h8256, hL]
  rcases Nat.lt_or_ge (csUse memory n j).toNat 1 with h | h
  · rw [show (csUse memory n j).toNat = 0 from by omega, if_pos rfl]
    norm_num
  · rw [show (csUse memory n j).toNat = 1 from by omega, if_neg (by norm_num)]
    norm_num



end Challenge.Modexp.Submission.Proofs.Fast.Csub
