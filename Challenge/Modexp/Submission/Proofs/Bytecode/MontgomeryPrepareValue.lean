import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperBlock

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryPrepareValue

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Montgomery

/-- Actual setup states: copy UNIT early and store the inverse word last. -/
def prepare (s : State) (n : Nat) (np : UInt256) : State :=
  let unit := MontgomeryWrapperBlock.unitSetupLeaf s n
  let acc := MontgomerySetupBlock.flatLeaf unit
    (BigHelpers.copyReturned unit 2048 7168 n 0 [])
  let r2 := MontgomeryWrapperValue.r2Leaf acc n np
  let encoded := MontgomeryWrapperValue.coreLeaf r2 1024 8192 3072 n np
  let base := MontgomerySetupBlock.flatLeaf encoded
    (BigHelpers.copyReturned encoded 1024 3072 n 0 [])
  MontgomeryWrapperBlock.storeNpLeaf base np

private theorem represents_low (before after : ByteArray) (p n value : Nat)
    (hp : p + 32 * n ≤ 3072)
    (hread : ∀ start size, start + size ≤ 3072 →
      MachineState.readPadded after start size = MachineState.readPadded before start size)
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

/-- Setup establishes both encoded inputs from only the initial base and modulus. -/
theorem prepare_correct (s : State) (n : Nat) (np : UInt256) (baseValue m : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32) (hm : 0 < m) (hodd : m % 2 = 1)
    (hinv : (m * np.toNat + 1) % (2 ^ 256) = 0)
    (hmod : Limbs.Represents s.memory 0 n m)
    (hbase : Limbs.Represents s.memory 1024 n baseValue) :
    Limbs.Represents (prepare s n np).memory 0 n m ∧
      Limbs.Represents (prepare s n np).memory 1024 n (Domain.encode m n baseValue) ∧
      Limbs.Represents (prepare s n np).memory 2048 n (Domain.encode m n 1) ∧
      MachineState.readWord (prepare s n np).memory 11264 = np := by
  let unit := MontgomeryWrapperBlock.unitSetupLeaf s n
  let acc := MontgomerySetupBlock.flatLeaf unit
    (BigHelpers.copyReturned unit 2048 7168 n 0 [])
  let r2 := MontgomeryWrapperValue.r2Leaf acc n np
  let encoded := MontgomeryWrapperValue.coreLeaf r2 1024 8192 3072 n np
  let baseState := MontgomerySetupBlock.flatLeaf encoded
    (BigHelpers.copyReturned encoded 1024 3072 n 0 [])

  have unitResult := MontgomeryOneCorrect.returned_correct s n m 0 []
    hn hN hm hmod.1 hodd hmod
  have hunit : Limbs.Represents unit.memory 7168 n (Domain.R n % m) := unitResult.1
  have hunitMod : Limbs.Represents unit.memory 0 n m := unitResult.2
  have hunitBase : Limbs.Represents unit.memory 1024 n baseValue :=
    MontgomeryOneCorrect.returned_preserves_region s n m 1024 baseValue 0 []
      hn hN hm hmod.1 hodd hmod
      ⟨Or.inr (by change 1024 + 32 * n ≤ 7168; omega),
        Or.inl (by change 1024 + 32 * n ≤ 5120; omega)⟩ hbase

  have hacc : Limbs.Represents acc.memory 2048 n (Domain.R n % m) :=
    BigHelpers.copyMemory_represents unit.memory 2048 7168 n (Domain.R n % m)
      hunit (by omega) (by omega) (Or.inl (by omega))
  have haccMod : Limbs.Represents acc.memory 0 n m :=
    BigHelpers.represents_copyMemory_disjoint_region unit.memory 2048 7168 0 n m
      (by omega) (Or.inr (by omega)) hunitMod
  have haccBase : Limbs.Represents acc.memory 1024 n baseValue :=
    BigHelpers.represents_copyMemory_disjoint_region unit.memory 2048 7168 1024 n baseValue
      (by omega) (Or.inr (by omega)) hunitBase
  have haccUnit : Limbs.Represents acc.memory 7168 n (Domain.R n % m) :=
    BigHelpers.represents_copyMemory_disjoint_region unit.memory 2048 7168 7168 n
      (Domain.R n % m) (by omega) (Or.inl (by omega)) hunit

  have r2Result := MontgomeryWrapperValue.r2Leaf_correct acc n m np
    hn hN hm hodd hinv haccUnit haccMod
  have hr2Mod : Limbs.Represents r2.memory 0 n m :=
    r2Result.2 0 m (by omega) haccMod
  have hr2Base : Limbs.Represents r2.memory 1024 n baseValue :=
    r2Result.2 1024 baseValue (by omega) haccBase
  have hr2Acc : Limbs.Represents r2.memory 2048 n (Domain.R n % m) :=
    r2Result.2 2048 (Domain.R n % m) (by omega) hacc
  have core := MontgomeryWrapperValue.coreLeaf_correct r2 1024 8192 3072 n np
    baseValue ((Domain.R n * Domain.R n) % m) m hN
    (by decide) (by decide) (by decide) (by decide)
    hr2Base r2Result.1 hr2Mod hm (Nat.mod_lt _ hm).le hinv
  have encodeValue :
      Domain.mont m np.toNat n baseValue ((Domain.R n * Domain.R n) % m) =
        Domain.encode m n baseValue :=
    Domain.mont_encode_input m np.toNat n baseValue hm hmod.1
      (Domain.coprime_R_of_odd m n hm hodd) hbase.1 hinv
  have hencoded : Limbs.Represents encoded.memory 3072 n (Domain.encode m n baseValue) := by
    rw [← encodeValue]
    exact core.1
  have hencodedMod : Limbs.Represents encoded.memory 0 n m :=
    represents_low _ _ 0 n m (by omega) core.2.2 hr2Mod
  have hencodedAcc : Limbs.Represents encoded.memory 2048 n (Domain.R n % m) :=
    represents_low _ _ 2048 n (Domain.R n % m) (by omega) core.2.2 hr2Acc

  have hbaseValue : Limbs.Represents baseState.memory 1024 n (Domain.encode m n baseValue) :=
    BigHelpers.copyMemory_represents encoded.memory 1024 3072 n (Domain.encode m n baseValue)
      hencoded (by omega) (by omega) (Or.inl (by omega))
  have hbaseMod : Limbs.Represents baseState.memory 0 n m :=
    BigHelpers.represents_copyMemory_disjoint_region encoded.memory 1024 3072 0 n m
      (by omega) (Or.inr (by omega)) hencodedMod
  have hbaseAcc : Limbs.Represents baseState.memory 2048 n (Domain.R n % m) :=
    BigHelpers.represents_copyMemory_disjoint_region encoded.memory 1024 3072 2048 n
      (Domain.R n % m) (by omega) (Or.inl (by omega)) hencodedAcc

  have storeLow (p value : Nat) (hp : p + 32 * n ≤ 3072)
      (hrep : Limbs.Represents baseState.memory p n value) :
      Limbs.Represents (MontgomeryWrapperBlock.storeNpLeaf baseState np).memory p n value := by
    apply represents_low _ _ p n value hp _ hrep
    intro start size hsize
    apply Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
    exact Or.inl (by omega)
  change Limbs.Represents (MontgomeryWrapperBlock.storeNpLeaf baseState np).memory 0 n m ∧
    Limbs.Represents (MontgomeryWrapperBlock.storeNpLeaf baseState np).memory
      1024 n (Domain.encode m n baseValue) ∧
    Limbs.Represents (MontgomeryWrapperBlock.storeNpLeaf baseState np).memory
      2048 n (Domain.encode m n 1) ∧
    MachineState.readWord (MontgomeryWrapperBlock.storeNpLeaf baseState np).memory 11264 = np
  refine ⟨storeLow 0 m (by omega) hbaseMod,
    storeLow 1024 (Domain.encode m n baseValue) (by omega) hbaseValue, ?_, ?_⟩
  · simpa only [Domain.encode, Nat.one_mul] using
      storeLow 2048 (Domain.R n % m) (by omega) hbaseAcc
  · exact Challenge.EvmProof.Memory.readWord_writeWord _ 11264 np

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryPrepareValue
