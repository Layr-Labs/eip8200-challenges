import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryBaseLoadValue
import Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryReadyValue

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Montgomery

def directReady (s : State) (offset length n : Nat) : State :=
  let cleared := OneMemory.clearLeaf s 3072 n 0 []
  let seeded := OneMemory.storeOneLeaf cleared 3072
  MontgomeryBaseLoadValue.loadBaseLeaf seeded offset length

def «initialize» (s : State) (n : Nat) (ret : UInt256)
    (saved : List UInt256) : State :=
  BigHelpers.addReturned s 2048 3072 1 0 n ret saved

private theorem seed_preserves_region (s : State) (n ptr value : Nat)
    (hN : n ≤ 32) (hbefore : ptr + 32 * n ≤ 3072)
    (hrep : Limbs.Represents s.memory ptr n value) :
    Limbs.Represents
      (OneMemory.storeOneLeaf (OneMemory.clearLeaf s 3072 n 0 []) 3072).memory
      ptr n value := by
  have hc := BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 ptr n
    value (by omega) (Or.inr hbefore) hrep
  refine ⟨hc.1, ?_⟩
  rw [← hc.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hjn := List.mem_range.mp hj
  apply congrArg UInt256.toNat
  change MachineState.readWord
    (MachineState.writeBytes (BigHelpers.clearMemory s.memory (UInt256.ofNat 3072) n)
      (Data.Bytes.natToBytesPadded 1 32) 3072) (ptr + 32 * j) = _
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
    (Or.inl (by omega))]

private theorem seed_represents_one (s : State) (n : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32) :
    Limbs.Represents
      (OneMemory.storeOneLeaf (OneMemory.clearLeaf s 3072 n 0 []) 3072).memory
      3072 n 1 := by
  let cleared := OneMemory.clearLeaf s 3072 n 0 []
  have hzero : Limbs.Represents cleared.memory 3072 n 0 :=
    BigHelpers.clearMemory_represents_zero s.memory 3072 n (by omega)
  have hread : (MachineState.readWord cleared.memory (3072 + 32 * 0)).toNat = 0 :=
    BigHelpers.readWord_clearMemory s.memory 3072 n 0 (by omega) (by omega)
  have hvalue := BigLoadCorrect.value_memoryLimbs_write_add cleared.memory 3072 n 0 1
    (by omega) (by rw [hread]; norm_num)
  rw [Limbs.value_of_represents hzero, Nat.zero_add, Nat.pow_zero, Nat.mul_one] at hvalue
  apply (Limbs.represents_iff_value
    (Nat.one_lt_pow (by omega) Limbs.radix_gt_one)).2
  change Nat.ofDigits Limbs.radix
    (Limbs.memoryLimbs
      (MachineState.writeBytes cleared.memory (Data.Bytes.natToBytesPadded 1 32) 3072)
      3072 n) = 1
  simpa only [hread, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using hvalue

private theorem load_preserves_represents (s : State)
    (offset length n ptr value : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32) (hoffset : offset < 2 ^ 256)
    (hlength : length ≤ 32 * n)
    (hdisjoint : ptr + 32 * n ≤ 1024 ∨
      1024 + 32 * Limbs.limbCount length ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr n value) :
    Limbs.Represents (MontgomeryBaseLoadValue.loadBaseLeaf s offset length).memory ptr n value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hjn := List.mem_range.mp hj
  apply congrArg UInt256.toNat
  unfold MachineState.readWord
  rw [MontgomeryBaseLoadValue.loadBase_preserves_region s offset length n (ptr + 32 * j) 32
    hn hN hoffset hlength (by
      rcases hdisjoint with hbefore | hafter
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))]

/-- The actual clear, literal-one store, and raw load establish all four regions. -/
theorem directReady_correct (s : State) (offset length n m : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32) (hoffset : offset < 2 ^ 256)
    (hlength : length ≤ 32 * n) (_hm : 0 < m)
    (hmodulus : Limbs.Represents s.memory 0 n m)
    (hbase : Limbs.Represents s.memory 1024 n 0)
    (hacc : Limbs.Represents s.memory 2048 n 0) :
    Limbs.Represents (directReady s offset length n).memory 0 n m ∧
    Limbs.Represents (directReady s offset length n).memory 1024 n
      (Precompile.bytesToNatPadded s.executionEnv.calldata offset length) ∧
    Limbs.Represents (directReady s offset length n).memory 2048 n 0 ∧
    Limbs.Represents (directReady s offset length n).memory 3072 n 1 := by
  let seeded := OneMemory.storeOneLeaf (OneMemory.clearLeaf s 3072 n 0 []) 3072
  have hmodSeed : Limbs.Represents seeded.memory 0 n m :=
    seed_preserves_region s n 0 m hN (by omega) hmodulus
  have hbaseSeed : Limbs.Represents seeded.memory 1024 n 0 :=
    seed_preserves_region s n 1024 0 hN (by omega) hbase
  have haccSeed : Limbs.Represents seeded.memory 2048 n 0 :=
    seed_preserves_region s n 2048 0 hN (by omega) hacc
  have honeSeed : Limbs.Represents seeded.memory 3072 n 1 :=
    seed_represents_one s n hn hN
  have hk : Limbs.limbCount length ≤ n := by unfold Limbs.limbCount; omega
  exact ⟨load_preserves_represents seeded offset length n 0 m hn hN hoffset hlength
      (Or.inl (by omega)) hmodSeed,
    MontgomeryBaseLoadValue.loadBase_correct seeded offset length n hn hN hoffset hlength hbaseSeed,
    load_preserves_represents seeded offset length n 2048 0 hn hN hoffset hlength
      (Or.inr (by omega)) haccSeed,
    load_preserves_represents seeded offset length n 3072 1 hn hN hoffset hlength
      (Or.inr (by omega)) honeSeed⟩

/-- Initialize the accumulator from a ready state without another base conversion. -/
theorem initialize_correct (s : State) (n base m : Nat) (ret : UInt256)
    (saved : List UInt256) (_hn : 1 ≤ n) (hN : n ≤ 32) (hm : 0 < m)
    (hmodulus : Limbs.Represents s.memory 0 n m)
    (hbase : Limbs.Represents s.memory 1024 n base)
    (hacc : Limbs.Represents s.memory 2048 n 0)
    (hone : Limbs.Represents s.memory 3072 n 1) :
    Limbs.Represents («initialize» s n ret saved).memory 2048 n (1 % m) ∧
    Limbs.Represents («initialize» s n ret saved).memory 1024 n base ∧
    Limbs.Represents («initialize» s n ret saved).memory 0 n m := by
  have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have hresult := BigHelpers.addReturned_represents_mod s 2048 3072 0 n 1 0 1 m
    ret saved (by omega) (by omega) (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    hacc hone hmodulus hm (by omega) hmodulus.1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [«initialize», h0, h1, h2048, h3072, Nat.zero_add, Nat.one_mul] using hresult
  · exact BigHelpers.addReturned_preserves_region s 2048 3072 1 0 1024 n base
      ret saved (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)) hbase
  · exact BigHelpers.addReturned_preserves_region s 2048 3072 1 0 0 n m
      ret saved (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)) hmodulus

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryReadyValue

