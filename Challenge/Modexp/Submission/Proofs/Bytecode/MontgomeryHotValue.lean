import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperBlock
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryInversePreservation

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryHotValue

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperBlock
open Challenge.Modexp.Submission.Proofs.Montgomery

def rho (m n x : Nat) : Nat :=
  if m % 2 = 1 then Domain.encode m n x else x

def hotEffects (s : State) (bPtr : UInt256) (n : Nat)
    (ret : UInt256) (saved : List UInt256) : Effects :=
  if n = 0 then effectsOf (normalReturned s bPtr n ret saved)
  else if 32 < n then effectsOf (normalReturned s bPtr n ret saved)
  else
    let touched := loadLowLeaf s 0
    if (MachineState.readWord s.memory 0).toNat % 2 = 0 then
      effectsOf (normalReturned touched bPtr n ret saved)
    else
      let cached := loadLowLeaf touched 11264
      effectsOf (MontgomeryWrapperValue.coreLeaf cached bPtr.toNat 2048 3072 n
        (MachineState.readWord cached.memory 11264))

def hotReturned (s : State) (bPtr : UInt256) (n : Nat)
    (ret : UInt256) (saved : List UInt256) : State :=
  returnedState s (hotEffects s bPtr n ret saved) ret saved

def hotCopied (s : State) (bPtr : UInt256) (n : Nat)
    (ret copyRet : UInt256) (saved : List UInt256) : State :=
  BigHelpers.copyReturned (hotReturned s bPtr n ret saved)
    2048 3072 n copyRet saved

private theorem positive_count (s : State) (n m : Nat)
    (hm : 0 < m) (hmod : Limbs.Represents s.memory 0 n m) : 1 ≤ n := by
  by_contra h
  have hn : n = 0 := by omega
  have hbound := hmod.1
  rw [hn, pow_zero] at hbound
  omega

private theorem represents_of_readPadded
    (before after : ByteArray) (p n value : Nat)
    (hp : p + 32 * n ≤ 3072)
    (hread : ∀ start size, start + size ≤ 3072 →
      MachineState.readPadded after start size =
        MachineState.readPadded before start size)
    (hrep : Limbs.Represents before p n value) :
    Limbs.Represents after p n value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hjlt := List.mem_range.mp hj
  apply congrArg UInt256.toNat
  unfold MachineState.readWord
  rw [hread (p + 32 * j) 32 (by omega)]

private theorem encode_mod (m n x : Nat) (_hm : 0 < m) :
    Domain.encode m n (x % m) = Domain.encode m n x := by
  simp [Domain.encode, Nat.mul_mod]

theorem hotReturned_correct (s : State) (bPtr : UInt256)
    (n acc base m : Nat) (ret : UInt256) (saved : List UInt256)
    (hN : n ≤ 32) (hbPtr : bPtr.toNat ≤ 2048) (hm : 0 < m) (hacc : acc < m)
    (haccRep : Limbs.Represents s.memory 2048 n (rho m n acc))
    (hbaseRep : Limbs.Represents s.memory bPtr.toNat n (rho m n base))
    (hmod : Limbs.Represents s.memory 0 n m)
    (hinv : m % 2 = 1 →
      (m * (MachineState.readWord s.memory 11264).toNat + 1) %
        (2 ^ 256) = 0) :
    Limbs.Represents (hotReturned s bPtr n ret saved).memory 3072 n
        (rho m n ((acc * base) % m)) ∧
      (acc * base) % m < m ∧
      (∀ p value, p + 32 * n ≤ 3072 →
        Limbs.Represents s.memory p n value →
        Limbs.Represents (hotReturned s bPtr n ret saved).memory p n value) ∧
      (m % 2 = 1 →
        MachineState.readWord (hotReturned s bPtr n ret saved).memory 11264 =
          MachineState.readWord s.memory 11264) := by
  have hn : 1 ≤ n := positive_count s n m hm hmod
  have hparity := modulusLow_parity s n m hn hmod
  have hzero : n ≠ 0 := by omega
  have hlarge : ¬32 < n := by omega
  unfold hotReturned hotEffects
  rw [if_neg hzero, if_neg hlarge]
  by_cases heven : (MachineState.readWord s.memory 0).toNat % 2 = 0
  · rw [if_pos heven]
    have hmodEven : m % 2 = 0 := by omega
    have hacc0 : Limbs.Represents s.memory 2048 n acc := by
      simpa [rho, hmodEven] using haccRep
    have hbase0 : Limbs.Represents s.memory bPtr.toNat n base := by
      simpa [rho, hmodEven] using hbaseRep
    have touchedAcc : Limbs.Represents (loadLowLeaf s 0).memory 2048 n acc := by
      simpa [loadLowLeaf] using hacc0
    have touchedBase : Limbs.Represents (loadLowLeaf s 0).memory bPtr.toNat n base := by
      simpa [loadLowLeaf] using hbase0
    have touchedMod : Limbs.Represents (loadLowLeaf s 0).memory 0 n m := by
      simpa [loadLowLeaf] using hmod
    have normal := normalReturned_correct (loadLowLeaf s 0) bPtr n acc base m
      ret saved hN hbPtr hm hacc touchedAcc touchedBase touchedMod
    refine ⟨?_, normal.2.1, ?_, ?_⟩
    · simpa [rho, hmodEven, returnedState, effectsOf] using normal.1
    · intro p value hp hrep
      exact normal.2.2 p value hp (by simpa [loadLowLeaf] using hrep)
    · intro hodd
      omega
  · rw [if_neg heven]
    have hodd : m % 2 = 1 := by omega
    have hmR : m < Domain.R n := by
      simpa [Domain.R, CIOS.B, Limbs.radix] using hmod.1
    have hcop : Nat.Coprime m (Domain.R n) :=
      Domain.coprime_R_of_odd m n hm hodd
    have haccEnc : Limbs.Represents s.memory 2048 n (Domain.encode m n acc) := by
      simpa [rho, hodd] using haccRep
    have hbaseEnc : Limbs.Represents s.memory bPtr.toNat n (Domain.encode m n base) := by
      simpa [rho, hodd] using hbaseRep
    have haccLe : Domain.encode m n acc ≤ m := by
      exact (Nat.mod_lt _ hm).le
    let touched := loadLowLeaf s 0
    let cached := loadLowLeaf touched 11264
    have cachedAcc : Limbs.Represents cached.memory 2048 n (Domain.encode m n acc) := by
      simpa [cached, touched, loadLowLeaf] using haccEnc
    have cachedBase : Limbs.Represents cached.memory bPtr.toNat n
        (Domain.encode m n base) := by
      simpa [cached, touched, loadLowLeaf] using hbaseEnc
    have cachedMod : Limbs.Represents cached.memory 0 n m := by
      simpa [cached, touched, loadLowLeaf] using hmod
    have cachedInv :
        (m * (MachineState.readWord cached.memory 11264).toNat + 1) %
          (2 ^ 256) = 0 := by
      simpa [cached, touched, loadLowLeaf] using hinv hodd
    have core := MontgomeryWrapperValue.coreLeaf_correct cached bPtr.toNat 2048 3072 n
      (MachineState.readWord cached.memory 11264)
      (Domain.encode m n base) (Domain.encode m n acc) m
      hN (by omega) (by omega) (by decide) (by decide)
      cachedBase cachedAcc cachedMod hm haccLe cachedInv
    have hencoded : Domain.encode m n (base * acc) =
        Domain.encode m n ((acc * base) % m) := by
      calc
        Domain.encode m n (base * acc) =
            Domain.encode m n ((base * acc) % m) :=
          (encode_mod m n (base * acc) hm).symm
        _ = Domain.encode m n ((acc * base) % m) := by
          rw [Nat.mul_comm base acc]
    have hvalue :
        Domain.mont m (MachineState.readWord cached.memory 11264).toNat n
            (Domain.encode m n base) (Domain.encode m n acc) =
          rho m n ((acc * base) % m) := by
      simpa [rho, hodd] using
        (Domain.mont_encode_mul m
          (MachineState.readWord cached.memory 11264).toNat n base acc
          hm hmR hcop cachedInv).trans hencoded
    have hcache := Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryInversePreservation.coreLeaf_inverse_word cached
      bPtr.toNat 2048 n (MachineState.readWord cached.memory 11264)
      (Domain.encode m n base) (Domain.encode m n acc) m
      hN (by omega) (by omega) cachedBase cachedAcc cachedMod hm haccLe cachedInv
    refine ⟨?_, Nat.mod_lt _ hm, ?_, ?_⟩
    · have coreValue : Limbs.Represents
          (MontgomeryWrapperValue.coreLeaf cached bPtr.toNat 2048 3072 n
            (MachineState.readWord cached.memory 11264)).memory 3072 n
          (rho m n ((acc * base) % m)) := by
        simpa [hvalue] using core.1
      simpa [returnedState, effectsOf, cached, touched, loadLowLeaf] using coreValue
    · intro p value hp hrep
      have cachedRep : Limbs.Represents cached.memory p n value := by
        simpa [cached, touched, loadLowLeaf] using hrep
      have coreRep := represents_of_readPadded cached.memory
        (MontgomeryWrapperValue.coreLeaf cached bPtr.toNat 2048 3072 n
          (MachineState.readWord cached.memory 11264)).memory p n value hp
        core.2.2 cachedRep
      simpa [returnedState, effectsOf, cached, touched, loadLowLeaf] using coreRep
    · intro _
      simpa [returnedState, effectsOf, cached, touched, loadLowLeaf] using hcache

theorem hotCopied_correct (s : State) (bPtr : UInt256)
    (n acc base m : Nat) (ret copyRet : UInt256) (saved : List UInt256)
    (hN : n ≤ 32) (hbPtr : bPtr.toNat ≤ 2048) (hm : 0 < m) (hacc : acc < m)
    (haccRep : Limbs.Represents s.memory 2048 n (rho m n acc))
    (hbaseRep : Limbs.Represents s.memory bPtr.toNat n (rho m n base))
    (hmod : Limbs.Represents s.memory 0 n m)
    (hinv : m % 2 = 1 →
      (m * (MachineState.readWord s.memory 11264).toNat + 1) %
        (2 ^ 256) = 0) :
    Limbs.Represents (hotCopied s bPtr n ret copyRet saved).memory 2048 n
        (rho m n ((acc * base) % m)) ∧
      (acc * base) % m < m ∧
      (∀ p value, p + 32 * n ≤ 2048 →
        Limbs.Represents s.memory p n value →
        Limbs.Represents (hotCopied s bPtr n ret copyRet saved).memory p n value) ∧
      (m % 2 = 1 →
        MachineState.readWord (hotCopied s bPtr n ret copyRet saved).memory 11264 =
          MachineState.readWord s.memory 11264) := by
  have hot := hotReturned_correct s bPtr n acc base m ret saved
    hN hbPtr hm hacc haccRep hbaseRep hmod hinv
  have copied := BigHelpers.copyMemory_represents
    (hotReturned s bPtr n ret saved).memory 2048 3072 n
      (rho m n ((acc * base) % m)) hot.1
      (by omega) (by omega) (Or.inl (by omega))
  refine ⟨?_, hot.2.1, ?_, ?_⟩
  · simpa [hotCopied, BigHelpers.copyReturned, Word.literal_eq_ofNat] using copied
  · intro p value hp hrep
    have before := hot.2.2.1 p value (by omega) hrep
    have preserved := BigHelpers.represents_copyMemory_disjoint_region
      (hotReturned s bPtr n ret saved).memory 2048 3072 p n value
      (by omega) (Or.inr (by omega)) before
    simpa [hotCopied, BigHelpers.copyReturned, Word.literal_eq_ofNat] using preserved
  · intro hodd
    have before := hot.2.2.2 hodd
    have copiedWord := BigHelpers.readWord_copyMemory_disjoint_region
      (hotReturned s bPtr n ret saved).memory 2048 3072 11264 (n + 1) n 0
      (by omega) (by omega) (by omega) (Or.inl (by omega))
    calc
      MachineState.readWord (hotCopied s bPtr n ret copyRet saved).memory 11264 =
          MachineState.readWord (hotReturned s bPtr n ret saved).memory 11264 := by
        simpa [hotCopied, BigHelpers.copyReturned, Word.literal_eq_ofNat] using copiedWord
      _ = MachineState.readWord s.memory 11264 := before

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryHotValue
