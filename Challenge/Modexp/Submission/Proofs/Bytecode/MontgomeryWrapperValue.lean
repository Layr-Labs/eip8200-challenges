import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock
import Challenge.Modexp.Submission.Proofs.Montgomery.CoreState
import Challenge.Modexp.Submission.Proofs.Montgomery.Setup

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperValue

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

private theorem reduceLayout (n : Nat) (hN : n ≤ 32) :
    Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryReduceBlock.Layout 9216 0 n := by
  exact ⟨by omega, by omega, by omega, Or.inr (by omega),
    Or.inl (by omega), Or.inr (by omega)⟩

theorem copyUnit_represents (s : State) (n value : Nat) (hn : n ≤ 32)
    (hunit : Limbs.Represents s.memory 7168 n value) :
    Limbs.Represents (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.copyUnitLeaf s n).memory 8192 n value := by
  exact Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers.copyMemory_represents s.memory 8192 7168 n value hunit
    (by norm_num; omega) (by norm_num; omega) (Or.inr (by omega))

theorem copyUnit_preserves_region (s : State) (n ptr value : Nat) (hn : n ≤ 32)
    (hdisjoint : 8192 + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ 8192)
    (hrep : Limbs.Represents s.memory ptr n value) :
    Limbs.Represents (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.copyUnitLeaf s n).memory ptr n value := by
  exact Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers.represents_copyMemory_disjoint_region s.memory 8192 7168 ptr n value
    (by norm_num; omega) hdisjoint hrep

theorem double_preserves_region (s : State) (n ptr value : Nat) (hn : n ≤ 32)
    (hR2 : 8192 + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ 8192)
    (hCandidate : ptr + 32 * n ≤ 5120 ∨ 5120 + 32 * n ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr n value) :
    Limbs.Represents (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.doubleLeaf s 0 n).memory ptr n value := by
  exact Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers.addReturned_preserves_region s 8192 8192 1 0 ptr n value 0 []
    (by norm_num; omega) (by norm_num; omega) hR2 hCandidate hrep

theorem double_represents (s : State) (n value m : Nat) (hn : n ≤ 32)
    (hrep : Limbs.Represents s.memory 8192 n value)
    (hmod : Limbs.Represents s.memory 0 n m)
    (hv : value < m) (hmR : m < Limbs.radix ^ n) :
    Limbs.Represents (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.doubleLeaf s 0 n).memory 8192 n ((2 * value) % m) := by
  have h := Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers.addReturned_represents_mod s 8192 8192 0 n 1 value value m 0 []
    (by decide) (by norm_num; omega) (by norm_num; omega)
    (by norm_num; omega) (by norm_num; omega) (Or.inl rfl)
    (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
    hrep hrep hmod hv hv.le hmR
  have hdst : UInt256.ofNat 8192 = (8192 : UInt256) := by decide
  have hone : UInt256.ofNat 1 = (1 : UInt256) := by decide
  have hzero : UInt256.ofNat 0 = (0 : UInt256) := by decide
  rw [hdst, hone, hzero] at h
  simpa only [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.doubleLeaf, Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.flatLeaf, Nat.one_mul, ← Nat.two_mul] using h

theorem doubleProgress_preserves_region (s : State) (n k ptr value : Nat) (hn : n ≤ 32)
    (hR2 : 8192 + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ 8192)
    (hCandidate : ptr + 32 * n ≤ 5120 ∨ 5120 + 32 * n ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr n value) :
    Limbs.Represents (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.doubleProgress s 0 n k).memory ptr n value := by
  induction k with
  | zero => exact hrep
  | succ k ih => exact double_preserves_region _ n ptr value hn hR2 hCandidate ih

theorem doubleIter_lt (m value k : Nat) (hm : 0 < m) (hv : value < m) :
    Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter m value k < m := by
  cases k with
  | zero => exact hv
  | succ k => exact Nat.mod_lt _ hm

theorem doubleProgress_represents (s : State) (n k value m : Nat) (hn : n ≤ 32)
    (hrep : Limbs.Represents s.memory 8192 n value)
    (hmod : Limbs.Represents s.memory 0 n m)
    (hv : value < m) (hmR : m < Limbs.radix ^ n) :
    Limbs.Represents (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.doubleProgress s 0 n k).memory 8192 n
      (Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter m value k) := by
  induction k with
  | zero => exact hrep
  | succ k ih =>
      have hmod' := doubleProgress_preserves_region s n k 0 m hn
        (Or.inr (by omega)) (Or.inl (by omega)) hmod
      exact double_represents _ n _ m hn ih hmod' (doubleIter_lt m value k (by omega) hv) hmR

theorem r2DoubledLeaf_represents (s : State) (n m : Nat) (hn : n ≤ 32)
    (hm : 0 < m) (hmR : m < Limbs.radix ^ n)
    (hunit : Limbs.Represents s.memory 7168 n (Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n % m))
    (hmod : Limbs.Represents s.memory 0 n m) :
    Limbs.Represents (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.r2DoubledLeaf s 0 n).memory 8192 n
      (Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter m (Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n % m) (2 * n)) := by
  apply doubleProgress_represents _ n (2 * n) _ m hn
  · exact copyUnit_represents s n _ hn hunit
  · exact copyUnit_preserves_region s n 0 m hn (Or.inr (by omega)) hmod
  · exact Nat.mod_lt _ hm
  · exact hmR

theorem r2DoubledLeaf_preserves_region (s : State) (n ptr value : Nat) (hn : n ≤ 32)
    (hR2 : 8192 + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ 8192)
    (hCandidate : ptr + 32 * n ≤ 5120 ∨ 5120 + 32 * n ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr n value) :
    Limbs.Represents (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.r2DoubledLeaf s 0 n).memory ptr n value := by
  apply doubleProgress_preserves_region _ n (2 * n) ptr value hn hR2 hCandidate
  exact copyUnit_preserves_region s n ptr value hn hR2 hrep


/-- Actual flat core stages. A finite execution certificate is still required separately. -/
def coreLeaf (s : State) (aPtr bPtr out n : Nat) (np : UInt256) : State :=
  let raw := Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s (UInt256.ofNat aPtr) (UInt256.ofNat bPtr)
    0 n np 0 [] n
  Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.finishLeaf raw (UInt256.ofNat out) 0 n 0 [] 0 []

private theorem progress_frame (s : State) (a b : UInt256) (n : Nat) (np : UInt256)
    (i : Nat) :
    { Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b 0 n np 0 [] i with
      memory := s.memory, activeWords := s.activeWords } = s := by
  induction i with
  | zero => cases s; rfl
  | succ i ih =>
      change { Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s a b 0 n np 0 [] i with
        memory := s.memory, activeWords := s.activeWords } = s
      exact ih

theorem coreLeaf_frame (s : State) (aPtr bPtr out n : Nat) (np : UInt256) :
    { coreLeaf s aPtr bPtr out n np with
      memory := s.memory, activeWords := s.activeWords } = s := by
  exact progress_frame s (UInt256.ofNat aPtr) (UInt256.ofNat bPtr) n np n

/-- Task22 supplies the actual raw State equality; Task20 supplies reduction and copying.
The left operand may be any represented n-limb value. The right operand may equal m.
Input aliasing is permitted. Only the required low regions are preserved. -/
theorem coreLeaf_correct (s : State) (aPtr bPtr out n : Nat) (np : UInt256)
    (aValue bValue m : Nat) (hN : n ≤ 32) (haPtr : aPtr ≤ 8192) (hbPtr : bPtr ≤ 8192)
    (hout : 3072 ≤ out) (houtUpper : out ≤ 8192)
    (ha : Limbs.Represents s.memory aPtr n aValue)
    (hb : Limbs.Represents s.memory bPtr n bValue)
    (hmemory : Limbs.Represents s.memory 0 n m) (hm : 0 < m) (hb_le : bValue ≤ m)
    (hinv : (m * np.toNat + 1) % (2^256) = 0) :
    Limbs.Represents (coreLeaf s aPtr bPtr out n np).memory out n
        (Challenge.Modexp.Submission.Proofs.Montgomery.Domain.mont m np.toNat n aValue bValue) ∧
      Challenge.Modexp.Submission.Proofs.Montgomery.Domain.mont m np.toNat n aValue bValue < m ∧
      (∀ p size, p + size ≤ 3072 →
        MachineState.readPadded (coreLeaf s aPtr bPtr out n np).memory p size =
          MachineState.readPadded s.memory p size) := by
  let raw := Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress s (UInt256.ofNat aPtr) (UInt256.ofNat bPtr)
    0 n np 0 [] n
  have hafit : aPtr + 32*n < 2^256 := by omega
  have hbfit : bPtr + 32*n < 2^256 := by omega
  have htfit : 9216 + 32*(n+2) < 2^256 := by omega
  have hpa : (UInt256.ofNat aPtr).toNat = aPtr := by
    change aPtr % (2^256) = aPtr
    exact Nat.mod_eq_of_lt (by omega)
  have hpb : (UInt256.ofNat bPtr).toNat = bPtr := by
    change bPtr % (2^256) = bPtr
    exact Nat.mod_eq_of_lt (by omega)
  have hpo : (UInt256.ofNat out).toNat = out := by
    change out % (2^256) = out
    exact Nat.mod_eq_of_lt (by omega)
  have hz : (0 : UInt256).toNat = 0 := rfl
  have hraw : raw.memory = Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.coreProgress
      s.memory aPtr bPtr 0 9216 n np n := by
    simpa only [hpa, hpb, hz] using
      (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.progress_memory_eq s (UInt256.ofNat aPtr) (UInt256.ofNat bPtr)
        0 n np 0 [] n hN (by rw [hpa]; change aPtr + 32*n < 2^256; exact hafit)
        (by rw [hpb]; change bPtr + 32*n < 2^256; exact hbfit)
        (by change 0 + 32*n < 2^256; omega)
        htfit (Nat.le_refl n))
  have result := Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult.coreResult_correct s.memory raw aPtr bPtr out 0 n
    np aValue bValue m 0 [] 0 [] ha hb hmemory hm hb_le hinv hafit hbfit
    (by change 0 + 32*n < 2^256; omega) htfit
    (Or.inl (by change aPtr + 32*n ≤ 9216; omega))
    (Or.inl (by change bPtr + 32*n ≤ 9216; omega))
    (Or.inl (by change 0 + 32*n ≤ 9216; omega)) hraw
    (reduceLayout n hN) (by change out + 32*n < 2^256; omega)
    (Or.inl (by change out + 32*n ≤ 9216; omega))
  have hfinish : (coreLeaf s aPtr bPtr out n np).memory =
      (Challenge.Modexp.Submission.Proofs.Montgomery.CoreResult.finishReturned raw out 0 n 0 [] 0 []).memory := by
    simpa only [coreLeaf, hpo, hz] using
      (Challenge.Modexp.Submission.Proofs.Montgomery.CoreState.finishLeaf_memory_eq raw (UInt256.ofNat out) 0 n 0 [] 0 [])
  rw [hfinish]
  refine ⟨result.2.1, result.2.2.1, ?_⟩
  intro p size hp
  apply Challenge.EvmProof.Memory.readPadded_congr
  intro i hi
  exact result.2.2.2.2 (p+i)
    (Or.inl (by change p+i < 9216; omega))
    (Or.inl (by change p+i < 5120; omega)) (Or.inl (by omega))


def squareStep (s : State) (n : Nat) (np : UInt256) : State :=
  Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.squareCopyLeaf (coreLeaf s 8192 8192 3072 n np) n

def squareProgress (s : State) (n : Nat) (np : UInt256) : Nat → State
  | 0 => s
  | k+1 => squareStep (squareProgress s n np k) n np

/-- The frozen factor2 plan: actual unit copy, 2*n doubles, and seven core/copy stages. -/
def r2Leaf (s : State) (n : Nat) (np : UInt256) : State :=
  squareProgress (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.r2DoubledLeaf s 0 n) n np 7

private theorem represents_low (before after : ByteArray) (p n value : Nat)
    (hp : p + 32*n ≤ 3072)
    (hread : ∀ start size, start + size ≤ 3072 →
      MachineState.readPadded after start size = MachineState.readPadded before start size)
    (hrep : Limbs.Represents before p n value) : Limbs.Represents after p n value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hjlt := List.mem_range.mp hj
  apply congrArg UInt256.toNat
  unfold MachineState.readWord
  rw [hread (p + 32*j) 32 (by omega)]

theorem squareStep_correct (s : State) (n value m : Nat) (np : UInt256)
    (hN : n ≤ 32) (hvalue : Limbs.Represents s.memory 8192 n value)
    (hmod : Limbs.Represents s.memory 0 n m) (hm : 0 < m) (hv : value < m)
    (hinv : (m * np.toNat + 1) % (2^256) = 0) :
    Limbs.Represents (squareStep s n np).memory 8192 n
        (Challenge.Modexp.Submission.Proofs.Montgomery.Domain.mont m np.toNat n value value) ∧
      Challenge.Modexp.Submission.Proofs.Montgomery.Domain.mont m np.toNat n value value < m ∧
      (∀ p v, p + 32*n ≤ 3072 → Limbs.Represents s.memory p n v →
        Limbs.Represents (squareStep s n np).memory p n v) := by
  have core := coreLeaf_correct s 8192 8192 3072 n np value value m
    hN (by decide) (by decide) (by decide) (by decide) hvalue hvalue hmod hm hv.le hinv
  refine ⟨Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.squareCopy_represents _ n _ hN core.1, core.2.1, ?_⟩
  intro p v hp hrep
  exact Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.squareCopy_preserves_low _ n p v hN hp
    (represents_low _ _ p n v hp core.2.2 hrep)

theorem squareProgress_correct (s : State) (n k value m : Nat) (np : UInt256)
    (hN : n ≤ 32) (hvalue : Limbs.Represents s.memory 8192 n value)
    (hmod : Limbs.Represents s.memory 0 n m) (hm : 0 < m) (hv : value < m)
    (hinv : (m * np.toNat + 1) % (2^256) = 0) :
    Limbs.Represents (squareProgress s n np k).memory 8192 n
        (Challenge.Modexp.Submission.Proofs.Montgomery.Setup.squareIter m np.toNat n value k) ∧
      Challenge.Modexp.Submission.Proofs.Montgomery.Setup.squareIter m np.toNat n value k < m ∧
      (∀ p v, p + 32*n ≤ 3072 → Limbs.Represents s.memory p n v →
        Limbs.Represents (squareProgress s n np k).memory p n v) := by
  induction k with
  | zero => exact ⟨hvalue, hv, fun _ _ _ h => h⟩
  | succ k ih =>
      have hmod' := ih.2.2 0 m (by omega) hmod
      have step := squareStep_correct (squareProgress s n np k) n
        (Challenge.Modexp.Submission.Proofs.Montgomery.Setup.squareIter m np.toNat n value k) m np hN ih.1 hmod' hm ih.2.1 hinv
      exact ⟨step.1, step.2.1, fun p v hp h => step.2.2 p v hp (ih.2.2 p v hp h)⟩

theorem r2Leaf_correct (s : State) (n m : Nat) (np : UInt256) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hm : 0 < m) (hodd : m % 2 = 1)
    (hinv : (m * np.toNat + 1) % (2^256) = 0)
    (hunit : Limbs.Represents s.memory 7168 n (Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n % m))
    (hmod : Limbs.Represents s.memory 0 n m) :
    Limbs.Represents (r2Leaf s n np).memory 8192 n
        ((Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n * Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n) % m) ∧
      (∀ p value, p + 32*n ≤ 3072 → Limbs.Represents s.memory p n value →
        Limbs.Represents (r2Leaf s n np).memory p n value) := by
  have doubled := r2DoubledLeaf_represents s n m hN hm hmod.1 hunit hmod
  have modAfter := r2DoubledLeaf_preserves_region s n 0 m hN
    (Or.inr (by omega)) (Or.inl (by omega)) hmod
  have squared := squareProgress_correct (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.r2DoubledLeaf s 0 n) n 7
    (Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter m (Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n % m) (2*n)) m np hN doubled modAfter hm
    (doubleIter_lt m _ (2*n) hm (Nat.mod_lt _ hm)) hinv
  have math : Challenge.Modexp.Submission.Proofs.Montgomery.Setup.squareIter m np.toNat n
      (Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter m (Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n % m) (2*n)) 7 =
        (Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n * Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n) % m := by
    simpa only [Challenge.Modexp.Submission.Proofs.Montgomery.Setup.fixedR2, Challenge.Modexp.Submission.Proofs.Montgomery.Domain.encode, Nat.one_mul,
      show 2^1 = 2 from rfl, show 8-1 = 7 from rfl] using
      (Challenge.Modexp.Submission.Proofs.Montgomery.Setup.fixedR2_correct m np.toNat n 1 hn hm hmod.1 hodd (by decide) hinv)
  refine ⟨?_, ?_⟩
  · rw [← math]
    exact squared.1
  · intro p value hp hrep
    exact squared.2.2 p value hp
      (r2DoubledLeaf_preserves_region s n p value hN
        (Or.inr (by omega)) (Or.inl (by omega)) hrep)


theorem squareProgress_frame (s : State) (n : Nat) (np : UInt256) (k : Nat) :
    { squareProgress s n np k with memory := s.memory, activeWords := s.activeWords } = s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change { coreLeaf (squareProgress s n np k) 8192 8192 3072 n np with
        memory := s.memory, activeWords := s.activeWords } = s
      have h := congrArg (fun t : State => { t with memory := s.memory, activeWords := s.activeWords })
        (coreLeaf_frame (squareProgress s n np k) 8192 8192 3072 n np)
      exact h.trans ih

theorem r2Leaf_frame (s : State) (n : Nat) (np : UInt256) :
    { r2Leaf s n np with memory := s.memory, activeWords := s.activeWords } = s := by
  have hs := congrArg (fun t : State => { t with memory := s.memory, activeWords := s.activeWords })
    (squareProgress_frame (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.r2DoubledLeaf s 0 n) n np 7)
  have hd := congrArg (fun t : State => { t with memory := s.memory, activeWords := s.activeWords })
    (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.doubleProgress_other_fields
      (Challenge.Modexp.Submission.Proofs.Bytecode.MontgomerySetupBlock.copyUnitLeaf s n) 0 n (2*n))
  exact hs.trans hd

/-- Actual R2 setup, encoding of a, then the core call with scanned operand b. -/
def productLeaf (s : State) (bPtr n : Nat) (np : UInt256) : State :=
  let r2 := r2Leaf s n np
  let encoded := coreLeaf r2 2048 8192 7168 n np
  coreLeaf encoded bPtr 7168 3072 n np

private theorem frame_trans (s t u : State)
    (ht : { t with memory := s.memory, activeWords := s.activeWords } = s)
    (hu : { u with memory := t.memory, activeWords := t.activeWords } = t) :
    { u with memory := s.memory, activeWords := s.activeWords } = s := by
  have h := congrArg (fun v : State => { v with memory := s.memory, activeWords := s.activeWords }) hu
  exact h.trans ht

theorem productLeaf_frame (s : State) (bPtr n : Nat) (np : UInt256) :
    { productLeaf s bPtr n np with memory := s.memory, activeWords := s.activeWords } = s := by
  let r2 := r2Leaf s n np
  let encoded := coreLeaf r2 2048 8192 7168 n np
  exact frame_trans s encoded (coreLeaf encoded bPtr 7168 3072 n np)
    (frame_trans s r2 encoded (r2Leaf_frame s n np)
      (coreLeaf_frame r2 2048 8192 7168 n np))
    (coreLeaf_frame encoded bPtr 7168 3072 n np)

/-- The scanned b operand may be unreduced. Modulus one and input aliasing are admitted. -/
theorem productLeaf_correct (s : State) (bPtr n a b m : Nat) (np : UInt256)
    (hbPtr : bPtr ≤ 2048) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hm : 0 < m) (hodd : m % 2 = 1) (ha : a < m) (hb : b < Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n)
    (hinv : (m * np.toNat + 1) % (2^256) = 0)
    (hunit : Limbs.Represents s.memory 7168 n (Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n % m))
    (hmod : Limbs.Represents s.memory 0 n m)
    (hamemory : Limbs.Represents s.memory 2048 n a)
    (hbmemory : Limbs.Represents s.memory bPtr n b) :
    Limbs.Represents (productLeaf s bPtr n np).memory 3072 n ((a*b)%m) ∧
      (a*b)%m < m ∧
      (∀ p value, p + 32*n ≤ 3072 → Limbs.Represents s.memory p n value →
        Limbs.Represents (productLeaf s bPtr n np).memory p n value) := by
  have hmR : m < Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n := hmod.1
  have hcop := Challenge.Modexp.Submission.Proofs.Montgomery.Domain.coprime_R_of_odd m n hm hodd
  have r2 := r2Leaf_correct s n m np hn hN hm hodd hinv hunit hmod
  have modR2 := r2.2 0 m (by omega) hmod
  have aR2 := r2.2 2048 a (by omega) hamemory
  have bR2 := r2.2 bPtr b (by omega) hbmemory
  have encoded := coreLeaf_correct (r2Leaf s n np) 2048 8192 7168 n np
    a ((Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n * Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n) % m) m
    hN (by decide) (by decide) (by decide) (by decide) aR2 r2.1 modR2 hm
    (Nat.mod_lt _ hm).le hinv
  have encodeEq :
      Challenge.Modexp.Submission.Proofs.Montgomery.Domain.mont m np.toNat n a
        ((Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n * Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R n) % m) =
          Challenge.Modexp.Submission.Proofs.Montgomery.Domain.encode m n a :=
    Challenge.Modexp.Submission.Proofs.Montgomery.Domain.mont_encode_input m np.toNat n a hm hmR hcop
      (lt_trans ha hmR) hinv
  rw [encodeEq] at encoded
  have modEncoded := represents_low _ _ 0 n m (by omega) encoded.2.2 modR2
  have bEncoded := represents_low _ _ bPtr n b (by omega) encoded.2.2 bR2
  have product := coreLeaf_correct (coreLeaf (r2Leaf s n np) 2048 8192 7168 n np)
    bPtr 7168 3072 n np b (Challenge.Modexp.Submission.Proofs.Montgomery.Domain.encode m n a) m
    hN (by omega) (by decide) (by decide) (by decide)
    bEncoded encoded.1 modEncoded hm encoded.2.1.le hinv
  have productEq := Challenge.Modexp.Submission.Proofs.Montgomery.Setup.mont_mixed_product
    m np.toNat n a b hm hmR hcop ha hb hinv
  rw [productEq] at product
  refine ⟨product.1, product.2.1, ?_⟩
  intro p value hp hrep
  exact represents_low _ _ p n value hp product.2.2
    (represents_low _ _ p n value hp encoded.2.2 (r2.2 p value hp hrep))

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWrapperValue
