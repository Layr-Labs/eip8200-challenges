import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperValue

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryInversePreservation

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Montgomery

/-- The actual core state preserves the padded inverse word outside its write regions. -/
theorem coreLeaf_inverse_word (s : State) (aPtr bPtr n : Nat) (np : UInt256)
    (aValue bValue m : Nat)
    (hN : n ≤ 32) (haPtr : aPtr ≤ 8192) (hbPtr : bPtr ≤ 8192)
    (ha : Limbs.Represents s.memory aPtr n aValue)
    (hb : Limbs.Represents s.memory bPtr n bValue)
    (hmemory : Limbs.Represents s.memory 0 n m)
    (hm : 0 < m) (hb_le : bValue ≤ m)
    (hinv : (m * np.toNat + 1) % (2 ^ 256) = 0) :
    MachineState.readWord
        (MontgomeryWrapperValue.coreLeaf s aPtr bPtr 3072 n np).memory 11264 =
      MachineState.readWord s.memory 11264 := by
  let raw := CoreState.progress s (UInt256.ofNat aPtr) (UInt256.ofNat bPtr)
    0 n np 0 [] n
  have hafit : aPtr + 32 * n < 2 ^ 256 := by omega
  have hbfit : bPtr + 32 * n < 2 ^ 256 := by omega
  have htfit : 9216 + 32 * (n + 2) < 2 ^ 256 := by omega
  have hpa : (UInt256.ofNat aPtr).toNat = aPtr := by
    change aPtr % (2 ^ 256) = aPtr
    exact Nat.mod_eq_of_lt (by omega)
  have hpb : (UInt256.ofNat bPtr).toNat = bPtr := by
    change bPtr % (2 ^ 256) = bPtr
    exact Nat.mod_eq_of_lt (by omega)
  have hz : (0 : UInt256).toNat = 0 := rfl
  have hpo : (UInt256.ofNat 3072).toNat = 3072 := by
    change 3072 % (2 ^ 256) = 3072
    exact Nat.mod_eq_of_lt (by omega)
  have hraw : raw.memory = CoreMemory.coreProgress
      s.memory aPtr bPtr 0 9216 n np n := by
    simpa only [hpa, hpb, hz] using
      (CoreState.progress_memory_eq s (UInt256.ofNat aPtr) (UInt256.ofNat bPtr)
        0 n np 0 [] n hN
        (by rw [hpa]; change aPtr + 32 * n < 2 ^ 256; exact hafit)
        (by rw [hpb]; change bPtr + 32 * n < 2 ^ 256; exact hbfit)
        (by change 0 + 32 * n < 2 ^ 256; omega) htfit (Nat.le_refl n))
  have layout : MontgomeryReduceBlock.Layout 9216 0 n :=
    ⟨by omega, by omega, by omega, Or.inr (by omega),
      Or.inl (by omega), Or.inr (by omega)⟩
  have result := CoreResult.coreResult_correct s.memory raw aPtr bPtr 3072 0 n
    np aValue bValue m 0 [] 0 [] ha hb hmemory hm hb_le hinv hafit hbfit
    (by change 0 + 32 * n < 2 ^ 256; omega) htfit
    (Or.inl (by change aPtr + 32 * n ≤ 9216; omega))
    (Or.inl (by change bPtr + 32 * n ≤ 9216; omega))
    (Or.inl (by change 0 + 32 * n ≤ 9216; omega)) hraw layout
    (by change 3072 + 32 * n < 2 ^ 256; omega)
    (Or.inl (by change 3072 + 32 * n ≤ 9216; omega))
  have hfinish : (MontgomeryWrapperValue.coreLeaf s aPtr bPtr 3072 n np).memory =
      (CoreResult.finishReturned raw 3072 0 n 0 [] 0 []).memory := by
    simpa only [MontgomeryWrapperValue.coreLeaf, hpo, hz] using
      (CoreState.finishLeaf_memory_eq raw (UInt256.ofNat 3072) 0 n 0 [] 0 [])
  rw [hfinish]
  unfold MachineState.readWord
  apply congrArg UInt256.ofNat
  apply congrArg Data.Bytes.bytesToBigEndianNat
  apply Challenge.EvmProof.Memory.readPadded_congr
  intro i _hi
  exact result.2.2.2.2 (11264 + i)
    (Or.inr (by change 9216 + 32 * (n + 2) ≤ 11264 + i; omega))
    (Or.inr (by change 5120 + 32 * n ≤ 11264 + i; omega))
    (Or.inr (by omega))

/-- Copying the core output back also preserves the inverse word, for any return frame. -/
theorem coreLeaf_copy_inverse_word (s : State) (aPtr bPtr n : Nat) (np : UInt256)
    (aValue bValue m : Nat) (ret : UInt256) (saved : List UInt256)
    (hN : n ≤ 32) (haPtr : aPtr ≤ 8192) (hbPtr : bPtr ≤ 8192)
    (ha : Limbs.Represents s.memory aPtr n aValue)
    (hb : Limbs.Represents s.memory bPtr n bValue)
    (hmemory : Limbs.Represents s.memory 0 n m)
    (hm : 0 < m) (hb_le : bValue ≤ m)
    (hinv : (m * np.toNat + 1) % (2 ^ 256) = 0) :
    MachineState.readWord
        (BigHelpers.copyReturned
          (MontgomeryWrapperValue.coreLeaf s aPtr bPtr 3072 n np)
          2048 3072 n ret saved).memory 11264 =
      MachineState.readWord s.memory 11264 := by
  -- The lemma's bound is n+1, but its actual copy iteration count remains n.
  -- This admits j=0 without requiring n>0 or changing the copy model.
  have hcopy := BigHelpers.readWord_copyMemory_disjoint_region
    (MontgomeryWrapperValue.coreLeaf s aPtr bPtr 3072 n np).memory
    2048 3072 11264 (n + 1) n 0 (by omega) (by omega)
    (by omega) (Or.inl (by omega))
  exact hcopy.trans
    (coreLeaf_inverse_word s aPtr bPtr n np aValue bValue m
      hN haPtr hbPtr ha hb hmemory hm hb_le hinv)

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryInversePreservation
