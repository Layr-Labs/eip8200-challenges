import Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory
import Challenge.Modexp.Submission.Proofs.Montgomery.Setup
import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryReduceBlock

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

abbrev B : Nat := Limbs.radix

def R (n : Nat) : Nat := B ^ n

def unit : Nat := 7168

def candidate : Nat := 5120

def DisjointSetup (n ptr : Nat) : Prop :=
  (unit + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ unit) ∧
  (ptr + 32 * n ≤ candidate ∨ candidate + 32 * n ≤ ptr)

def V (memory : ByteArray) (ptr count : Nat) : Nat :=
  Nat.ofDigits B (Limbs.memoryLimbs memory ptr count)

def flatLeaf (s result : State) : State :=
  { s with memory := result.memory, activeWords := result.activeWords }

def clearLeaf (s : State) (ptr count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  flatLeaf s (BigHelpers.clearReturned s (UInt256.ofNat ptr) count returnDest rest)

def storeOneMemory (memory : ByteArray) (ptr : Nat) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded 1 32) ptr

def storeOneActiveWords (activeWords : UInt256) (ptr : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.activeWordsAfter activeWords.toNat ptr 32)

def storeOneLeaf (s : State) (ptr : Nat) : State :=
  { s with memory := storeOneMemory s.memory ptr
           activeWords := storeOneActiveWords s.activeWords ptr }

def reduceLeaf (s : State) (dst modulus : Nat) (high : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  flatLeaf s (MontgomeryReduceBlock.reduceReturned s (UInt256.ofNat dst)
    (UInt256.ofNat modulus) high count returnDest rest)

def doubleLeaf (s : State) (dst modulus count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  flatLeaf s (BigHelpers.addReturned s (UInt256.ofNat dst) (UInt256.ofNat dst)
    (UInt256.ofNat 1) (UInt256.ofNat modulus) count returnDest rest)

def doubleProgress (s : State) (dst modulus count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : Nat → State
  | 0 => s
  | k + 1 => doubleLeaf
      (doubleProgress s dst modulus count returnDest rest k)
      dst modulus count returnDest rest

def makeMontgomeryOne (s : State) (modulus n : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let cleared := clearLeaf s unit n returnDest rest
  let top := MachineState.readWord cleared.memory (modulus + 32 * (n - 1))
  if 2 ^ 255 ≤ top.toNat then
    reduceLeaf cleared unit modulus (UInt256.ofNat 1) n returnDest rest
  else
    let seeded := storeOneLeaf cleared unit
    let reduced := reduceLeaf seeded unit modulus (UInt256.ofNat 0) n returnDest rest
    doubleProgress reduced unit modulus n returnDest rest (256 * n)

theorem unit_fit (n : Nat) (hn : n ≤ 32) :
    unit + 32 * n < 2 ^ 256 := by
  norm_num [unit]
  omega

theorem candidate_fit (n : Nat) (hn : n ≤ 32) :
    candidate + 32 * n < 2 ^ 256 := by
  norm_num [candidate]
  omega

theorem one_lt_R (n : Nat) (hn : 1 ≤ n) : 1 < R n := by
  cases n with
  | zero => omega
  | succ n =>
      rw [R, pow_succ]
      have hB : 1 < B := by norm_num [B, Limbs.radix]
      have hpow : 0 < B ^ n := pow_pos (by exact Limbs.radix_pos) _
      have hone : 1 ≤ B ^ n := by omega
      calc
        1 < B := hB
        _ ≤ B ^ n * B := by
          simpa using Nat.mul_le_mul_right B hone

theorem setup_layout (n : Nat) (hn : n ≤ 32) :
    MontgomeryReduceBlock.Layout unit 0 n := by
  constructor
  · exact unit_fit n hn
  · calc
      0 + 32 * n = 32 * n := by omega
      32 * n ≤ 1024 := by omega
      _ < 2 ^ 256 := by norm_num
  · exact candidate_fit n hn
  · norm_num [unit, candidate]
    omega
  · norm_num [unit, candidate]
    omega
  · norm_num [unit]
    omega

theorem setup_disjoint_zero (n : Nat) (hn : n ≤ 32) : DisjointSetup n 0 := by
  constructor
  · right
    norm_num [unit]
    omega
  · left
    norm_num [candidate]
    omega

theorem doubleIter_lt (m v : Nat) (hm : 0 < m) (hv : v < m) :
    ∀ k, Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter m v k < m
  | 0 => hv
  | k + 1 => by
      simp [Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter]
      exact Nat.mod_lt _ hm

theorem reduceLeaf_represents_mod (s : State) (n m total : Nat)
    (high : UInt256) (hn : n ≤ 32)
    (hm : 0 < m) (hmR : m < R n) (htotal : total < 2 * m)
    (hunit : Limbs.Represents s.memory unit n (total % R n))
    (hmodulus : Limbs.Represents s.memory 0 n m)
    (hhigh : high.toNat = total / R n)
    (returnDest : UInt256) (rest : List UInt256) :
    Limbs.Represents
      (reduceLeaf s unit 0 high n returnDest rest).memory unit n (total % m) := by
  have h := MontgomeryReduceBlock.reduceReturned_represents_mod s unit 0 n total m
    high returnDest rest (setup_layout n hn) hm hmR htotal hunit hmodulus hhigh
  simpa [reduceLeaf, flatLeaf, R] using h

theorem reduceLeaf_preserves_region (s : State) (n ptr regionCount value : Nat)
    (high : UInt256) (hn : n ≤ 32)
    (hdisjoint : unit + 32 * n ≤ ptr ∨ ptr + 32 * regionCount ≤ unit)
    (hcandidate : ptr + 32 * regionCount ≤ candidate ∨
      candidate + 32 * n ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr regionCount value)
    (returnDest : UInt256) (rest : List UInt256) :
    Limbs.Represents
      (reduceLeaf s unit 0 high n returnDest rest).memory ptr regionCount value := by
  have hcandidate' : candidate + 32 * n ≤ ptr ∨
      ptr + 32 * regionCount ≤ candidate := by
    rcases hcandidate with h | h
    · exact Or.inr h
    · exact Or.inl h
  have h := MontgomeryReduceBlock.reduceReturned_preserves_region s unit 0 n
    ptr regionCount value high returnDest rest (unit_fit n hn)
    (candidate_fit n hn) hdisjoint hcandidate' hrep
  simpa [reduceLeaf, flatLeaf] using h

theorem doubleLeaf_represents_mod (s : State) (n m value : Nat)
    (hn : n ≤ 32) (_hm : 0 < m) (hmR : m < R n)
    (hunit : Limbs.Represents s.memory unit n value)
    (hmodulus : Limbs.Represents s.memory 0 n m) (hvalue : value < m)
    (returnDest : UInt256) (rest : List UInt256) :
    Limbs.Represents
      (doubleLeaf s unit 0 n returnDest rest).memory unit n ((value + value) % m) := by
  have hlayout := setup_layout n hn
  have h := BigHelpers.addReturned_represents_mod s unit unit 0 n 1 value value m
    returnDest rest (by norm_num) hlayout.dstFit hlayout.dstFit hlayout.modulusFit
    hlayout.candidateFit (Or.inl rfl) hlayout.dstModulus hlayout.dstCandidate
    hlayout.modulusCandidate hunit hunit hmodulus hvalue hvalue.le hmR
  simpa [doubleLeaf, flatLeaf] using h

theorem doubleLeaf_preserves_region (s : State) (n ptr value : Nat)
    (hn : n ≤ 32) (hdisjoint : DisjointSetup n ptr)
    (hrep : Limbs.Represents s.memory ptr n value)
    (returnDest : UInt256) (rest : List UInt256) :
    Limbs.Represents
      (doubleLeaf s unit 0 n returnDest rest).memory ptr n value := by
  have hlayout := setup_layout n hn
  have h := BigHelpers.addReturned_preserves_region s unit unit 1 0 ptr n value
    returnDest rest hlayout.dstFit hlayout.candidateFit hdisjoint.1 hdisjoint.2 hrep
  simpa [doubleLeaf, flatLeaf] using h

theorem doubleProgress_correct (s : State) (n m value : Nat)
    (hn : n ≤ 32) (hm : 0 < m) (hmR : m < R n)
    (hunit : Limbs.Represents s.memory unit n value)
    (hmodulus : Limbs.Represents s.memory 0 n m) (hvalue : value < m)
    (returnDest : UInt256) (rest : List UInt256) :
    ∀ k, Limbs.Represents
        (doubleProgress s unit 0 n returnDest rest k).memory unit n
        (Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter m value k) ∧
      Limbs.Represents
        (doubleProgress s unit 0 n returnDest rest k).memory 0 n m := by
  intro k
  induction k with
  | zero => exact ⟨hunit, hmodulus⟩
  | succ k ih =>
      have hprevValue := doubleIter_lt m value hm hvalue k
      have hunit' := doubleLeaf_represents_mod
        (doubleProgress s unit 0 n returnDest rest k) n m
        (Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter m value k) hn hm hmR ih.1 ih.2 hprevValue
        returnDest rest
      have hmodulus' := doubleLeaf_preserves_region
        (doubleProgress s unit 0 n returnDest rest k) n 0 m hn
        (setup_disjoint_zero n hn) ih.2 returnDest rest
      constructor
      · simpa [doubleProgress, Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter, two_mul] using hunit'
      · simpa [doubleProgress] using hmodulus'

theorem doubleProgress_preserves_region (s : State) (n ptr value : Nat)
    (hn : n ≤ 32) (hdisjoint : DisjointSetup n ptr)
    (hrep : Limbs.Represents s.memory ptr n value)
    (returnDest : UInt256) (rest : List UInt256) :
    ∀ k, Limbs.Represents
      (doubleProgress s unit 0 n returnDest rest k).memory ptr n value := by
  intro k
  induction k with
  | zero => exact hrep
  | succ k ih =>
      exact doubleLeaf_preserves_region
        (doubleProgress s unit 0 n returnDest rest k) n ptr value hn
        hdisjoint ih returnDest rest

theorem doubleIter_radix (m n : Nat) (hm : 0 < m) :
    Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter m (1 % m) (256 * n) = R n % m := by
  have h := Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter_encode m 0 1 (256 * n) hm
  have hpow : (2 : Nat) ^ (256 * n) = R n := by
    simpa [R, B, Limbs.radix] using (pow_mul (2 : Nat) 256 n)
  simpa [Challenge.Modexp.Submission.Proofs.Montgomery.Domain.encode, Challenge.Modexp.Submission.Proofs.Montgomery.Domain.R, hpow] using h

theorem reduceLeaf_modulus (s : State) (n m _total : Nat) (high : UInt256)
    (hn : n ≤ 32) (hmodulus : Limbs.Represents s.memory 0 n m)
    (returnDest : UInt256) (rest : List UInt256) :
    Limbs.Represents
      (reduceLeaf s unit 0 high n returnDest rest).memory 0 n m := by
  apply reduceLeaf_preserves_region s n 0 n m high hn
  · exact (setup_disjoint_zero n hn).1
  · exact (setup_disjoint_zero n hn).2
  · exact hmodulus

theorem flatLeaf_memory (s result : State) :
    (flatLeaf s result).memory = result.memory := rfl

theorem flatLeaf_activeWords (s result : State) :
    (flatLeaf s result).activeWords = result.activeWords := rfl

theorem flatLeaf_other_fields (s result : State) :
    (flatLeaf s result).pc = s.pc ∧
    (flatLeaf s result).stack = s.stack ∧
    (flatLeaf s result).execLength = s.execLength ∧
    (flatLeaf s result).halt = s.halt ∧
    (flatLeaf s result).callStack = s.callStack ∧
    (flatLeaf s result).gasAvailable = s.gasAvailable ∧
    (flatLeaf s result).returnData = s.returnData ∧
    (flatLeaf s result).hReturn = s.hReturn ∧
    (flatLeaf s result).accountMap = s.accountMap ∧
    (flatLeaf s result).substate = s.substate ∧
    (flatLeaf s result).executionEnv = s.executionEnv := by
  simp [flatLeaf]

theorem clearLeaf_zero (s : State) (n : Nat) (hn : n ≤ 32)
    (returnDest : UInt256) (rest : List UInt256) :
    Limbs.Represents (clearLeaf s unit n returnDest rest).memory unit n 0 := by
  change Limbs.Represents
    (BigHelpers.clearMemory s.memory (UInt256.ofNat unit) n) unit n 0
  exact BigHelpers.clearMemory_represents_zero s.memory unit n (unit_fit n hn)

theorem clearLeaf_preserves_region (s : State) (n ptr value : Nat)
    (hn : n ≤ 32)
    (hdisjoint : unit + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ unit)
    (hrep : Limbs.Represents s.memory ptr n value)
    (returnDest : UInt256) (rest : List UInt256) :
    Limbs.Represents
      (clearLeaf s unit n returnDest rest).memory ptr n value := by
  change Limbs.Represents
    (BigHelpers.clearMemory s.memory (UInt256.ofNat unit) n) ptr n value
  exact BigHelpers.represents_clearMemory_disjoint_region s.memory unit ptr n
    value (unit_fit n hn) hdisjoint hrep

theorem clearLeaf_modulus (s : State) (n m : Nat) (hn : n ≤ 32)
    (hmodulus : Limbs.Represents s.memory 0 n m)
    (returnDest : UInt256) (rest : List UInt256) :
    Limbs.Represents
      (clearLeaf s unit n returnDest rest).memory 0 n m := by
  apply clearLeaf_preserves_region s n 0 m hn
  · right
    norm_num [unit]
    omega
  · exact hmodulus

theorem storeOne_memoryLimbs (memory : ByteArray) (n : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32) :
    Limbs.memoryLimbs (storeOneMemory
      (BigHelpers.clearMemory memory (UInt256.ofNat unit) n) unit) unit n =
      1 :: List.replicate (n - 1) 0 := by
  apply List.ext_get
  · simp only [Limbs.length_memoryLimbs, List.length_cons,
      List.length_replicate]
    omega
  · intro i hiLeft hiRight
    have hi : i < n := by simpa using hiLeft
    by_cases hi0 : i = 0
    · subst i
      simp [Limbs.memoryLimbs, storeOneMemory,
        Challenge.EvmProof.Memory.readWord_writeBytes_of_lt]
    · have hz := BigHelpers.readWord_clearMemory memory unit n i
          (unit_fit n hN) hi
      have hreadNat :
          (MachineState.readWord
            (storeOneMemory
              (BigHelpers.clearMemory memory (UInt256.ofNat unit) n) unit)
            (unit + 32 * i)).toNat = 0 := by
        unfold storeOneMemory
        rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact hz
        · simp [Data.Bytes.natToBytesPadded, ByteArray.size]
          omega
      have hi1 : 1 ≤ i := by omega
      simp only [Limbs.memoryLimbs] at hiLeft ⊢
      simp only [List.get_eq_getElem]
      rw [List.getElem_map (h := hiLeft)]
      simp only [List.getElem_range]
      change (MachineState.readWord
        (storeOneMemory
          (BigHelpers.clearMemory memory (UInt256.ofNat unit) n) unit)
        (unit + 32 * i)).toNat = _
      rw [hreadNat]
      cases i with
      | zero => omega
      | succ j => simp

theorem storeOne_represents_one (s : State) (n : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32)
    (returnDest : UInt256) (rest : List UInt256) :
    Limbs.Represents
      (storeOneLeaf (clearLeaf s unit n returnDest rest) unit).memory unit n 1 := by
  apply (Limbs.represents_iff_value (by
    have hR := one_lt_R n hn
    simpa [R] using hR)).2
  change Nat.ofDigits B (Limbs.memoryLimbs
    (storeOneMemory
      (BigHelpers.clearMemory s.memory (UInt256.ofNat unit) n) unit) unit n) = 1
  rw [storeOne_memoryLimbs s.memory n hn hN]
  rw [Nat.ofDigits_cons, Nat.ofDigits_replicate_zero]
  simp

theorem storeOne_preserves_region (s : State) (n ptr value : Nat)
    (_hn : n ≤ 32)
    (hdisjoint : unit + 32 * n ≤ ptr ∨ ptr + 32 * n ≤ unit)
    (hrep : Limbs.Represents s.memory ptr n value) :
    Limbs.Represents (storeOneLeaf s unit).memory ptr n value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  change (MachineState.readWord (storeOneMemory s.memory unit)
      (ptr + 32 * i)).toNat =
    (MachineState.readWord s.memory (ptr + 32 * i)).toNat
  unfold storeOneMemory
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  rcases hdisjoint with h | h
  · omega
  · omega

theorem clearLeaf_topWord (s : State) (n : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32)
    (returnDest : UInt256) (rest : List UInt256) :
    MachineState.readWord (clearLeaf s unit n returnDest rest).memory
        (32 * (n - 1)) =
      MachineState.readWord s.memory (32 * (n - 1)) := by
  change MachineState.readWord
      (BigHelpers.clearMemory s.memory (UInt256.ofNat unit) n)
      (32 * (n - 1)) = _
  have hdisjoint : 0 + 32 * n ≤ unit := by
    norm_num [unit]
    omega
  simpa only [Nat.zero_add] using
    (BigHelpers.readWord_clearMemory_disjoint_region s.memory unit 0 n n
      (n - 1) (by omega) (by omega) (unit_fit n hN) (Or.inr hdisjoint))

theorem top_value_bridge (s : State) (n m : Nat) (hn : 1 ≤ n)
    (hmodulus : Limbs.Represents s.memory 0 n m) :
    (MachineState.readWord s.memory (32 * (n - 1))).toNat =
      (m / B ^ (n - 1)) % B := by
  simpa [B] using Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.represented_digit hmodulus (by omega)

theorem top_value_after_clear (s : State) (n m : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32)
    (hmodulus : Limbs.Represents s.memory 0 n m)
    (returnDest : UInt256) (rest : List UInt256) :
    (MachineState.readWord
      (clearLeaf s unit n returnDest rest).memory (32 * (n - 1))).toNat =
      (m / B ^ (n - 1)) % B := by
  rw [clearLeaf_topWord s n hn hN returnDest rest]
  exact top_value_bridge s n m hn hmodulus

theorem strict_fast_bound (n m : Nat) (hn : 1 ≤ n)
    (hmR : m < R n) (hodd : m % 2 = 1)
    (htop : 2 ^ 255 ≤ (m / B ^ (n - 1)) % B) :
    R n < 2 * m := by
  let p := B ^ (n - 1)
  have hp : 0 < p := pow_pos (by exact Limbs.radix_pos) _
  have hR : R n = B * p := by
    unfold R
    calc
      B ^ n = B ^ ((n - 1) + 1) := by congr 1; omega
      _ = B ^ (n - 1) * B := by rw [pow_succ]
      _ = B * p := by simp [p, Nat.mul_comm]
  have hq : m / p < B := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    calc
      m < R n := hmR
      _ = B * p := hR
  have htop' : 2 ^ 255 ≤ m / p := by
    have hmod : (m / B ^ (n - 1)) % B = m / B ^ (n - 1) := by
      simpa [p] using (Nat.mod_eq_of_lt hq)
    rw [hmod] at htop
    simpa [p] using htop
  have hBhalf : B ≤ 2 * (m / p) := by
    norm_num [B, Limbs.radix] at htop' ⊢
    omega
  have hle : R n ≤ 2 * m := by
    rw [hR]
    calc
      B * p ≤ (2 * (m / p)) * p := Nat.mul_le_mul_right p hBhalf
      _ = 2 * (p * (m / p)) := by ring
      _ ≤ 2 * m := Nat.mul_le_mul_left 2 (by
        simpa [Nat.mul_comm] using (Nat.mul_div_le m p))
  by_contra hnot
  have heq : R n = 2 * m := by omega
  have h4B : ∃ q : Nat, B = 4 * q := by
    refine ⟨2 ^ 254, ?_⟩
    norm_num [B, Limbs.radix]
  have h4R : ∃ q : Nat, R n = 4 * q := by
    rcases h4B with ⟨q, hqB⟩
    cases n with
    | zero => omega
    | succ k =>
        refine ⟨q * B ^ k, ?_⟩
        simp only [R, pow_succ]
        rw [hqB]
        ring
  rcases h4R with ⟨q, hqR⟩
  have hmEven : m = 2 * q := by omega
  have hmMod : m % 2 = 0 := by simp [hmEven]
  omega

theorem slow_total_bound (m : Nat) (hm : 0 < m) : 1 < 2 * m := by omega

theorem slow_low_bound (n : Nat) (hn : 1 ≤ n) : 1 < R n := one_lt_R n hn

theorem makeMontgomeryOne_correct (s : State) (n m : Nat)
    (hn : 1 ≤ n) (hN : n ≤ 32) (hm : 0 < m) (hmR : m < R n)
    (hodd : m % 2 = 1) (hmodulus : Limbs.Represents s.memory 0 n m)
    (returnDest : UInt256) (rest : List UInt256) :
    let result := makeMontgomeryOne s 0 n returnDest rest
    Limbs.Represents result.memory unit n (R n % m) ∧
      Limbs.Represents result.memory 0 n m := by
  let cleared := clearLeaf s unit n returnDest rest
  have hclearUnit : Limbs.Represents cleared.memory unit n 0 := by
    exact clearLeaf_zero s n hN returnDest rest
  have hclearMod : Limbs.Represents cleared.memory 0 n m := by
    exact clearLeaf_modulus s n m hN hmodulus returnDest rest
  have htop := top_value_after_clear s n m hn hN hmodulus returnDest rest
  have htop' :
      (MachineState.readWord cleared.memory (0 + 32 * (n - 1))).toNat =
        (m / B ^ (n - 1)) % B := by
    simpa [cleared] using htop
  by_cases hfast : 2 ^ 255 ≤
      (MachineState.readWord
        (clearLeaf s unit n returnDest rest).memory (0 + 32 * (n - 1))).toNat
  · have htopFast : 2 ^ 255 ≤ (m / B ^ (n - 1)) % B := by
      have hfast' : 2 ^ 255 ≤
          (MachineState.readWord cleared.memory (0 + 32 * (n - 1))).toNat := by
        simpa [cleared] using hfast
      rw [← htop']
      exact hfast'
    have htotal : R n < 2 * m := strict_fast_bound n m hn hmR hodd htopFast
    have hRpos : 0 < R n := pow_pos (by exact Limbs.radix_pos) _
    have hunit : Limbs.Represents cleared.memory unit n (R n % R n) := by
      simpa using hclearUnit
    have hhigh : (UInt256.ofNat 1).toNat = R n / R n := by
      have hdiv : R n / R n = 1 := Nat.div_self hRpos
      simp [hdiv]
    have hresult := reduceLeaf_represents_mod cleared n m (R n)
      (UInt256.ofNat 1) hN hm hmR htotal hunit hclearMod hhigh returnDest rest
    have hmodulus' := reduceLeaf_modulus cleared n m (R n) (UInt256.ofNat 1)
      hN hclearMod returnDest rest
    simp only [makeMontgomeryOne]
    rw [if_pos hfast]
    simpa [cleared] using And.intro hresult hmodulus'
  · have hseed := storeOne_represents_one s n hn hN returnDest rest
    have hseedMod := storeOne_preserves_region cleared n 0 m hN
      (setup_disjoint_zero n hN).1 hclearMod
    have honeR : 1 < R n := one_lt_R n hn
    have hunit : Limbs.Represents
        (storeOneLeaf cleared unit).memory unit n (1 % R n) := by
      simpa [Nat.mod_eq_of_lt honeR] using hseed
    have hhigh : (UInt256.ofNat 0).toNat = 1 / R n := by
      simp [Nat.div_eq_of_lt honeR]
    have hred := reduceLeaf_represents_mod (storeOneLeaf cleared unit) n m 1
      (UInt256.ofNat 0) hN hm hmR (slow_total_bound m hm) hunit hseedMod hhigh
      returnDest rest
    have hredMod := reduceLeaf_modulus (storeOneLeaf cleared unit) n m 1
      (UInt256.ofNat 0) hN hseedMod returnDest rest
    have hdp := doubleProgress_correct
      (reduceLeaf (storeOneLeaf cleared unit) unit 0 (UInt256.ofNat 0) n
        returnDest rest) n m (1 % m) hN hm hmR hred hredMod
      (Nat.mod_lt 1 hm) returnDest rest (256 * n)
    have hvalue : Challenge.Modexp.Submission.Proofs.Montgomery.Setup.doubleIter m (1 % m) (256 * n) = R n % m :=
      doubleIter_radix m n hm
    have hresult : Limbs.Represents
        (doubleProgress
          (reduceLeaf (storeOneLeaf cleared unit) unit 0 (UInt256.ofNat 0) n
            returnDest rest)
          unit 0 n returnDest rest (256 * n)).memory unit n (R n % m) := by
      simpa [hvalue] using hdp.1
    simp only [makeMontgomeryOne]
    rw [if_neg hfast]
    simpa [cleared, hvalue] using And.intro hresult hdp.2

theorem makeMontgomeryOne_preserves_region (s : State) (n m ptr value : Nat)
    (_hn : 1 ≤ n) (hN : n ≤ 32) (_hm : 0 < m) (_hmR : m < R n)
    (_hodd : m % 2 = 1) (hmodulus : Limbs.Represents s.memory 0 n m)
    (hdisjoint : DisjointSetup n ptr)
    (hrep : Limbs.Represents s.memory ptr n value)
    (returnDest : UInt256) (rest : List UInt256) :
    Limbs.Represents
      (makeMontgomeryOne s 0 n returnDest rest).memory ptr n value := by
  let cleared := clearLeaf s unit n returnDest rest
  have hclearMod : Limbs.Represents cleared.memory 0 n m := by
    exact clearLeaf_modulus s n m hN hmodulus returnDest rest
  have hclearRep : Limbs.Represents cleared.memory ptr n value := by
    exact clearLeaf_preserves_region s n ptr value hN hdisjoint.1 hrep returnDest rest
  by_cases hfast : 2 ^ 255 ≤
      (MachineState.readWord
        (clearLeaf s unit n returnDest rest).memory (0 + 32 * (n - 1))).toNat
  · simp only [makeMontgomeryOne]
    rw [if_pos hfast]
    simpa [cleared] using
      (reduceLeaf_preserves_region cleared n ptr n value (UInt256.ofNat 1) hN
        hdisjoint.1 hdisjoint.2 hclearRep returnDest rest)
  · have hseedMod := storeOne_preserves_region cleared n 0 m hN
      (setup_disjoint_zero n hN).1 hclearMod
    have hseedRep := storeOne_preserves_region cleared n ptr value hN
      hdisjoint.1 hclearRep
    have hredMod := reduceLeaf_preserves_region
      (storeOneLeaf cleared unit) n 0 n m (UInt256.ofNat 0) hN
      (setup_disjoint_zero n hN).1 (setup_disjoint_zero n hN).2 hseedMod
      returnDest rest
    have hredRep := reduceLeaf_preserves_region
      (storeOneLeaf cleared unit) n ptr n value (UInt256.ofNat 0) hN
      hdisjoint.1 hdisjoint.2 hseedRep returnDest rest
    have hdp := doubleProgress_preserves_region
      (reduceLeaf (storeOneLeaf cleared unit) unit 0 (UInt256.ofNat 0) n
        returnDest rest) n ptr value hN hdisjoint hredRep returnDest rest (256 * n)
    simp only [makeMontgomeryOne]
    rw [if_neg hfast]
    simpa [cleared] using hdp

theorem flatLeaf_eq_update (s result : State) :
    flatLeaf s result = { s with memory := result.memory, activeWords := result.activeWords } := rfl

end Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory
