import Challenge.Modexp.Submission.Proofs.Bytecode.BitPrefix
import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseLoop
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-!
# Functional correctness of multi-limb base conversion

Base conversion runs in two phases.  A prefix of `direct` base bytes is loaded
straight into the reduced-base register by the certified `loadBigEndian`
helper; the remaining bytes go through the original bitwise Horner loop.

Soundness of the first phase is an *inequality*: `256 ^ direct ≤ modulus`,
which holds because `direct` is either `0` or `32 * (count - 1)` with the
modulus's top limb nonzero.  Nothing here has to characterise `direct` exactly;
a smaller `direct` would only be slower.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseCorrect

open EvmSemantics
open EvmSemantics.EVM

open BigBase

/-! ## Limb-representation glue -/

theorem limbDigits_zero (count : Nat) :
    Limbs.limbDigits count 0 = List.replicate count 0 := by
  simp [Limbs.limbDigits, Nat.digitsAppend]

theorem memoryLimbs_split (memory : ByteArray) (ptr k d : Nat) :
    Limbs.memoryLimbs memory ptr (k + d) =
      Limbs.memoryLimbs memory ptr k ++
        (List.range d).map
          (fun i => (MachineState.readWord memory (ptr + 32 * (k + i))).toNat) := by
  simp only [Limbs.memoryLimbs, List.range_add, List.map_append, List.map_map]
  rfl

theorem ofDigits_map_range_zero (b d : Nat) (f : Nat → Nat)
    (h : ∀ i, i < d → f i = 0) :
    Nat.ofDigits b ((List.range d).map f) = 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [List.range_succ, List.map_append, Nat.ofDigits_append,
        ih (fun i hi => h i (by omega))]
      simp [h d (by omega)]

theorem represents_zero_read (memory : ByteArray) (ptr count j : Nat)
    (hj : j < count) (hrep : Limbs.Represents memory ptr count 0) :
    (MachineState.readWord memory (ptr + 32 * j)).toNat = 0 := by
  have h := hrep.2
  rw [limbDigits_zero] at h
  have hmem : (MachineState.readWord memory (ptr + 32 * j)).toNat ∈
      Limbs.memoryLimbs memory ptr count := by
    simp only [Limbs.memoryLimbs, List.mem_map]
    exact ⟨j, by simpa using hj, rfl⟩
  rw [h] at hmem
  exact List.eq_of_mem_replicate hmem

theorem radix_pow_pos (count : Nat) : (0 : Nat) < Limbs.radix ^ count := by
  induction count with
  | zero => simp
  | succ k ih => rw [pow_succ]; exact Nat.mul_pos ih Limbs.radix_pos

theorem represents_zero_of_reads (memory : ByteArray) (ptr count : Nat)
    (h : ∀ j, j < count → (MachineState.readWord memory (ptr + 32 * j)).toNat = 0) :
    Limbs.Represents memory ptr count 0 := by
  refine (Limbs.represents_iff_value (radix_pow_pos count)).2 ?_
  simp only [Limbs.memoryLimbs]
  exact ofDigits_map_range_zero _ _ _ h

theorem represents_zero_truncate (memory : ByteArray) (ptr k count : Nat)
    (hk : k ≤ count) (hrep : Limbs.Represents memory ptr count 0) :
    Limbs.Represents memory ptr k 0 :=
  represents_zero_of_reads memory ptr k
    fun j hj => represents_zero_read memory ptr count j (by omega) hrep

theorem represents_extend (memory : ByteArray) (ptr k d value : Nat)
    (hvalue : value < Limbs.radix ^ (k + d))
    (hlow : Limbs.Represents memory ptr k value)
    (hhigh : ∀ i, i < d →
      (MachineState.readWord memory (ptr + 32 * (k + i))).toNat = 0) :
    Limbs.Represents memory ptr (k + d) value := by
  refine (Limbs.represents_iff_value hvalue).2 ?_
  rw [memoryLimbs_split, Nat.ofDigits_append,
    ofDigits_map_range_zero _ _ _ hhigh, Nat.mul_zero, Nat.add_zero]
  exact Limbs.value_of_represents hlow

/-- A nonzero top limb forces the represented value above `radix ^ (count-1)`. -/
theorem radix_pow_le_of_top_limb (memory : ByteArray) (ptr count value : Nat)
    (hcount : 0 < count)
    (hrep : Limbs.Represents memory ptr count value)
    (hnz : (MachineState.readWord memory (ptr + 32 * (count - 1))).toNat ≠ 0) :
    Limbs.radix ^ (count - 1) ≤ value := by
  obtain ⟨k, rfl⟩ : ∃ k, count = k + 1 := ⟨count - 1, by omega⟩
  have hvalue := Limbs.value_of_represents hrep
  rw [memoryLimbs_split memory ptr k 1, Nat.ofDigits_append] at hvalue
  simp only [Limbs.length_memoryLimbs] at hvalue
  have hone : Nat.ofDigits Limbs.radix ((List.range 1).map
      (fun i => (MachineState.readWord memory (ptr + 32 * (k + i))).toNat)) =
      (MachineState.readWord memory (ptr + 32 * k)).toNat := by
    simp
  rw [hone] at hvalue
  have hnz' : 1 ≤ (MachineState.readWord memory (ptr + 32 * k)).toNat := by
    simp only [Nat.add_sub_cancel] at hnz
    omega
  have hmul : Limbs.radix ^ k * 1 ≤
      Limbs.radix ^ k * (MachineState.readWord memory (ptr + 32 * k)).toNat :=
    Nat.mul_le_mul_left _ hnz'
  simp only [Nat.add_sub_cancel]
  omega

/-! ## The directly loaded prefix -/

theorem topOffset_eq (count : Nat) (hpos : 0 < count) (hle : count ≤ 32) :
    topOffset count = 32 * (count - 1) := by
  have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h5 : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hsub : UInt256.ofNat count - UInt256.ofNat 1 = UInt256.ofNat (count - 1) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  unfold topOffset topOffsetWord
  rw [h1, hsub, h5,
    Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega) (by
      have : count - 1 ≤ 31 := by omega
      calc (count - 1) * 2 ^ 5 ≤ 31 * 2 ^ 5 := Nat.mul_le_mul_right _ this
        _ < 2 ^ 256 := by norm_num),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by
      have : count - 1 ≤ 31 := by omega
      calc (count - 1) * 2 ^ 5 ≤ 31 * 2 ^ 5 := Nat.mul_le_mul_right _ this
        _ < 2 ^ 256 := by norm_num)]
  omega

theorem directValue_le_topOffset (memory : ByteArray) (count baseSize : Nat) :
    directValue memory count baseSize ≤ topOffset count := by
  unfold directValue
  have h := directTake_le_one memory count baseSize
  calc directTake memory count baseSize * topOffset count
      ≤ 1 * topOffset count := Nat.mul_le_mul_right _ h
    _ = topOffset count := Nat.one_mul _

theorem readWord_ne_zero_of_directValue_pos (memory : ByteArray)
    (count baseSize : Nat) (h : 0 < directValue memory count baseSize) :
    (MachineState.readWord memory (topOffset count)).toNat ≠ 0 := by
  intro hz
  unfold directValue directTake at h
  rw [if_pos hz] at h
  simp at h

/-- The directly loaded prefix is a residue.  This is the whole soundness
argument for the optimisation, and it is an inequality. -/
theorem pow_directValue_le (memory : ByteArray) (count baseSize modulus : Nat)
    (hpos : 0 < count) (hle : count ≤ 32) (hmod : 0 < modulus)
    (hrep : Limbs.Represents memory 0 count modulus) :
    256 ^ (directValue memory count baseSize) ≤ modulus := by
  rcases Nat.eq_zero_or_pos (directValue memory count baseSize) with h | h
  · rw [h, show (256 : Nat) ^ 0 = 1 by norm_num]
    omega
  · have hnz := readWord_ne_zero_of_directValue_pos memory count baseSize h
    rw [topOffset_eq count hpos hle] at hnz
    have hkey := radix_pow_le_of_top_limb memory 0 count modulus hpos hrep
      (by simpa using hnz)
    have hd : directValue memory count baseSize ≤ 32 * (count - 1) := by
      have hle' := directValue_le_topOffset memory count baseSize
      rwa [topOffset_eq count hpos hle] at hle'
    calc 256 ^ (directValue memory count baseSize)
        ≤ 256 ^ (32 * (count - 1)) := Nat.pow_le_pow_right (by omega) hd
      _ = Limbs.radix ^ (count - 1) := (Limbs.pow_radix (count - 1)).symm
      _ ≤ modulus := hkey

theorem limbCount_directValue_le (memory : ByteArray) (count baseSize : Nat)
    (hpos : 0 < count) (hle : count ≤ 32) :
    Limbs.limbCount (directValue memory count baseSize) ≤ count := by
  have hd : directValue memory count baseSize ≤ 32 * (count - 1) := by
    have hle' := directValue_le_topOffset memory count baseSize
    rwa [topOffset_eq count hpos hle] at hle'
  unfold Limbs.limbCount
  omega

/-! ## Bit-level progress (unchanged apart from the new return addresses) -/

theorem baseBit_toNat_le_one (byte : UInt256) (j : Nat) :
    (baseBit byte j).toNat ≤ 1 := by
  rw [baseBit, Challenge.EvmProof.Word.word_toNat_land,
    show (1 : UInt256).toNat = 1 by decide]
  exact Nat.and_le_right

theorem baseBit_toNat_eq (byte : UInt256) (j : Nat) (hj : j < 8) :
    (baseBit byte j).toNat = BitPrefix.exponentBitNat byte j := by
  have hsame : baseBit byte j = ExpCore.exponentBit byte j := by rfl
  rw [hsame]
  exact BigExponentCorrect.exponentBit_toNat_eq byte j hj

def baseBitStep (modulus : Nat) (byte : UInt256) (j acc : Nat) : Nat :=
  (2 * acc + (baseBit byte j).toNat) % modulus

def baseBitAfter (modulus : Nat) (byte : UInt256) : Nat → Nat → Nat
  | 0, acc => acc
  | j + 1, acc => baseBitStep modulus byte j
      (baseBitAfter modulus byte j acc)

theorem baseBitStep_lt (modulus : Nat) (byte : UInt256) (j acc : Nat)
    (hmodulusPos : 0 < modulus) : baseBitStep modulus byte j acc < modulus :=
  Nat.mod_lt _ hmodulusPos

theorem baseBitAfter_lt (modulus : Nat) (byte : UInt256) (steps acc : Nat)
    (hmodulusPos : 0 < modulus) (hacc : acc < modulus) :
    baseBitAfter modulus byte steps acc < modulus := by
  induction steps with
  | zero => exact hacc
  | succ steps ih => exact baseBitStep_lt modulus byte steps _ hmodulusPos

theorem bitProgress_represents (s : State) (count : Nat) (byte : UInt256)
    (steps acc modulus : Nat) (hsteps : steps ≤ 8) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulus) (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 1024 count acc)
    (hone : Limbs.Represents s.memory 3072 count 1)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := bitProgress count byte steps s
    Limbs.Represents progress.memory 1024 count
        (baseBitAfter modulus byte steps acc) ∧
      Limbs.Represents progress.memory 3072 count 1 ∧
      Limbs.Represents progress.memory 0 count modulus := by
  induction steps with
  | zero => exact ⟨hacc, hone, hmodulus⟩
  | succ steps ih =>
      let before := bitProgress count byte steps s
      let beforeValue := baseBitAfter modulus byte steps acc
      let doubled := BigHelpers.addReturned before 1024 1024 1 0 count 1721 []
      let bit := (baseBit byte steps).toNat
      have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
      have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
      have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
      have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
      have h1721 : (1721 : UInt256) = UInt256.ofNat 1721 := by decide
      have h1746 : (1746 : UInt256) = UInt256.ofNat 1746 := by decide
      have hbefore := ih (by omega)
      have hbeforeReduced : beforeValue < modulus :=
        baseBitAfter_lt modulus byte steps acc hmodulusPos haccReduced
      have hdoubled : Limbs.Represents doubled.memory 1024 count
          ((beforeValue + beforeValue) % modulus) := by
        simpa [doubled, h0, h1, h1024, h1721] using
          BigHelpers.addReturned_represents_mod before 1024 1024 0 count 1
            beforeValue beforeValue modulus 1721 [] (by omega) (by omega)
            (by omega) (by omega) (by omega) (Or.inl rfl) (Or.inr (by omega))
            (Or.inl (by omega)) (Or.inl (by omega)) hbefore.1 hbefore.1
            hbefore.2.2 hbeforeReduced hbeforeReduced.le hbefore.2.2.1
      have hdoubledOne : Limbs.Represents doubled.memory 3072 count 1 := by
        simpa [doubled, h0, h1, h1024, h1721] using
          BigHelpers.addReturned_preserves_region before 1024 1024 1 0 3072
            count 1 1721 [] (by omega) (by omega) (Or.inl (by omega))
            (Or.inl (by omega)) hbefore.2.1
      have hdoubledModulus : Limbs.Represents doubled.memory 0 count modulus := by
        simpa [doubled, h0, h1, h1024, h1721] using
          BigHelpers.addReturned_preserves_region before 1024 1024 1 0 0
            count modulus 1721 [] (by omega) (by omega) (Or.inr (by omega))
            (Or.inl (by omega)) hbefore.2.2
      have hdoubleReduced : (beforeValue + beforeValue) % modulus < modulus :=
        Nat.mod_lt _ hmodulusPos
      have hbitLe : bit ≤ 1 := baseBit_toNat_le_one byte steps
      let after := BigHelpers.addReturned doubled 1024 3072
        (baseBit byte steps) 0 count 1746 []
      have hbitWord : baseBit byte steps = UInt256.ofNat bit :=
        Challenge.EvmProof.Word.word_eq_ofNat_toNat _
      have hafterEq : after = BigHelpers.addReturned doubled
          (UInt256.ofNat 1024) (UInt256.ofNat 3072) (UInt256.ofNat bit)
          (UInt256.ofNat 0) count (UInt256.ofNat 1746) [] := by
        simp only [after]
        rw [hbitWord, h0, h1024, h3072, h1746]
      have hafter : Limbs.Represents after.memory 1024 count
          ((((beforeValue + beforeValue) % modulus) + bit) % modulus) := by
        rw [hafterEq]
        simpa only [Nat.mul_one] using
          BigHelpers.addReturned_represents_mod doubled 1024 3072 0 count bit
            ((beforeValue + beforeValue) % modulus) 1 modulus
            (UInt256.ofNat 1746) [] hbitLe
            (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
            (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
            hdoubled hdoubledOne hdoubledModulus hdoubleReduced
            (by omega) hdoubledModulus.1
      have hafterOne : Limbs.Represents after.memory 3072 count 1 := by
        rw [hafterEq]
        exact
          BigHelpers.addReturned_preserves_region doubled 1024 3072 bit 0 3072
            count 1 (UInt256.ofNat 1746) [] (by omega) (by omega)
            (Or.inl (by omega))
            (Or.inl (by omega)) hdoubledOne
      have hafterModulus : Limbs.Represents after.memory 0 count modulus := by
        rw [hafterEq]
        exact
          BigHelpers.addReturned_preserves_region doubled 1024 3072 bit 0 0
            count modulus (UInt256.ofNat 1746) [] (by omega) (by omega)
            (Or.inr (by omega))
            (Or.inl (by omega)) hdoubledModulus
      have hvalue :
          (((beforeValue + beforeValue) % modulus) + bit) % modulus =
            baseBitStep modulus byte steps beforeValue := by
        calc
          (((beforeValue + beforeValue) % modulus) + bit) % modulus =
              ((beforeValue + beforeValue) + bit) % modulus :=
            Nat.mod_add_mod _ _ _
          _ = baseBitStep modulus byte steps beforeValue := by
            simp only [baseBitStep, bit]
            congr 2
            omega
      rw [hvalue] at hafter
      simpa [bitProgress, before, doubled, after, beforeValue,
        baseBitAfter] using ⟨hafter, hafterOne, hafterModulus⟩

theorem bitProgress_preserves_2048 (s : State) (count : Nat)
    (byte : UInt256) (steps value : Nat) (hsteps : steps ≤ 8)
    (hcount : count ≤ 32)
    (hrep : Limbs.Represents s.memory 2048 count value) :
    Limbs.Represents (bitProgress count byte steps s).memory 2048 count value := by
  induction steps with
  | zero => exact hrep
  | succ steps ih =>
      let before := bitProgress count byte steps s
      let doubled := BigHelpers.addReturned before 1024 1024 1 0 count 1721 []
      let bit := (baseBit byte steps).toNat
      let after := BigHelpers.addReturned doubled 1024 3072
        (baseBit byte steps) 0 count 1746 []
      have hbefore := ih (by omega)
      have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
      have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
      have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
      have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
      have h1721 : (1721 : UInt256) = UInt256.ofNat 1721 := by decide
      have h1746 : (1746 : UInt256) = UInt256.ofNat 1746 := by decide
      have hdoubled : Limbs.Represents doubled.memory 2048 count value := by
        simpa [doubled, h0, h1, h1024, h1721] using
          BigHelpers.addReturned_preserves_region before 1024 1024 1 0 2048
            count value (UInt256.ofNat 1721) [] (by omega) (by omega)
            (Or.inl (by omega)) (Or.inl (by omega)) hbefore
      have hbitWord : baseBit byte steps = UInt256.ofNat bit :=
        Challenge.EvmProof.Word.word_eq_ofNat_toNat _
      have hafterEq : after = BigHelpers.addReturned doubled
          (UInt256.ofNat 1024) (UInt256.ofNat 3072) (UInt256.ofNat bit)
          (UInt256.ofNat 0) count (UInt256.ofNat 1746) [] := by
        simp only [after]
        rw [hbitWord, h0, h1024, h3072, h1746]
      have hafter : Limbs.Represents after.memory 2048 count value := by
        rw [hafterEq]
        exact BigHelpers.addReturned_preserves_region doubled 1024 3072
          bit 0 2048 count value (UInt256.ofNat 1746) [] (by omega) (by omega)
          (Or.inl (by omega)) (Or.inl (by omega)) hdoubled
      simpa [bitProgress, before, doubled, after] using hafter

theorem baseBitAfter_eq (modulus : Nat) (byte : UInt256) (steps acc : Nat)
    (hsteps : steps ≤ 8) (hacc : acc < modulus) :
    baseBitAfter modulus byte steps acc =
      (acc * 2 ^ steps + BitPrefix.bitPrefix byte steps) % modulus := by
  induction steps with
  | zero => simp [baseBitAfter, BitPrefix.bitPrefix, Nat.mod_eq_of_lt hacc]
  | succ steps ih =>
      let value := acc * 2 ^ steps + BitPrefix.bitPrefix byte steps
      let bit := (baseBit byte steps).toNat
      have hbit : bit = BitPrefix.exponentBitNat byte steps :=
        baseBit_toNat_eq byte steps (by omega)
      have hmul : (2 * (value % modulus)) % modulus =
          (2 * value) % modulus := by
        calc
          (2 * (value % modulus)) % modulus =
              (2 % modulus * ((value % modulus) % modulus)) % modulus :=
            Nat.mul_mod _ _ _
          _ = (2 % modulus * (value % modulus)) % modulus := by
            rw [Nat.mod_mod]
          _ = (2 * value) % modulus := (Nat.mul_mod _ _ _).symm
      rw [baseBitAfter, baseBitStep, ih (by omega)]
      calc
        (2 * (value % modulus) + bit) % modulus =
            ((2 * (value % modulus)) % modulus + bit) % modulus := by
          rw [Nat.mod_add_mod]
        _ = ((2 * value) % modulus + bit) % modulus := by rw [hmul]
        _ = (2 * value + bit) % modulus := Nat.mod_add_mod _ _ _
        _ = (acc * 2 ^ (steps + 1) +
              BitPrefix.bitPrefix byte (steps + 1)) % modulus := by
          simp only [value, bit, BitPrefix.bitPrefix, hbit, pow_succ]
          congr 1
          ring

theorem baseBitAfter_eight (modulus : Nat) (byte : UInt256) (acc : Nat)
    (hacc : acc < modulus) (hbyte : byte.toNat < 256) :
    baseBitAfter modulus byte 8 acc =
      (acc * 256 + byte.toNat) % modulus := by
  rw [baseBitAfter_eq modulus byte 8 acc (by omega) hacc,
    BitPrefix.bitPrefix_eight byte hbyte]
  norm_num

theorem loadedBaseByte_lt (s : State) (baseOff i : Nat) :
    (loadedBaseByte s baseOff i).toNat < 256 := by
  change (ExpCore.loadedExponentByte s baseOff i).toNat < 256
  exact BigExponentCorrect.loadedExponentByte_lt s baseOff i

/-! ## Byte-level progress from an arbitrary start index -/

def baseValueSeq (s : State) (modulus baseOff start acc : Nat) : Nat → Nat
  | 0 => acc
  | i + 1 =>
      (baseValueSeq s modulus baseOff start acc i * 256 +
        (loadedBaseByte s baseOff (start + i)).toNat) % modulus

def baseValueAfter (s : State) (modulus baseOff steps : Nat) : Nat :=
  baseValueSeq s modulus baseOff 0 0 steps

theorem baseValueSeq_lt (s : State) (modulus baseOff start acc steps : Nat)
    (hmodulusPos : 0 < modulus) (hacc : acc < modulus) :
    baseValueSeq s modulus baseOff start acc steps < modulus := by
  cases steps with
  | zero => simpa [baseValueSeq] using hacc
  | succ steps =>
      rw [baseValueSeq]
      exact Nat.mod_lt _ hmodulusPos

theorem baseValueAfter_lt (s : State) (modulus baseOff steps : Nat)
    (hmodulusPos : 0 < modulus) :
    baseValueAfter s modulus baseOff steps < modulus :=
  baseValueSeq_lt s modulus baseOff 0 0 steps hmodulusPos hmodulusPos

/-- Restarting the Horner fold at index `d` with the value produced by the first
`d` bytes agrees with running it straight through. -/
theorem baseValueSeq_shift (s : State) (modulus baseOff d acc k : Nat) :
    baseValueSeq s modulus baseOff d
        (baseValueSeq s modulus baseOff 0 acc d) k =
      baseValueSeq s modulus baseOff 0 acc (d + k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [baseValueSeq, ih, show d + (k + 1) = (d + k) + 1 by omega,
        baseValueSeq, Nat.zero_add]

theorem baseProgressFrom_represents (s : State)
    (count baseOff start steps modulus acc : Nat)
    (hcount : count ≤ 32) (hmodulusPos : 0 < modulus) (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 1024 count acc)
    (hone : Limbs.Represents s.memory 3072 count 1)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := BigBaseLoop.baseProgressFrom count baseOff start steps s
    Limbs.Represents progress.memory 1024 count
        (baseValueSeq s modulus baseOff start acc steps) ∧
      Limbs.Represents progress.memory 3072 count 1 ∧
      Limbs.Represents progress.memory 0 count modulus := by
  induction steps with
  | zero => exact ⟨hacc, hone, hmodulus⟩
  | succ steps ih =>
      let before := BigBaseLoop.baseProgressFrom count baseOff start steps s
      let beforeValue := baseValueSeq s modulus baseOff start acc steps
      let byte := loadedBaseByte before baseOff (start + steps)
      have hbefore := ih
      have hbeforeReduced : beforeValue < modulus :=
        baseValueSeq_lt s modulus baseOff start acc steps hmodulusPos haccReduced
      have hbyte : byte = loadedBaseByte s baseOff (start + steps) := by
        exact BigBaseLoop.loadedBaseByte_baseProgressFrom count baseOff start
          (start + steps) steps s
      have hbits := bitProgress_represents before count byte 8 beforeValue
        modulus (by omega) hcount hmodulusPos hbeforeReduced hbefore.1
        hbefore.2.1 hbefore.2.2
      have hbyteLt : byte.toNat < 256 := by
        rw [hbyte]
        exact loadedBaseByte_lt s baseOff (start + steps)
      have heq := baseBitAfter_eight modulus byte beforeValue hbeforeReduced
        hbyteLt
      rw [heq] at hbits
      simpa [BigBaseLoop.baseProgressFrom, baseValueSeq, before, beforeValue,
        byte, hbyte] using hbits

theorem baseProgressFrom_preserves_2048 (s : State)
    (count baseOff start steps value : Nat) (hcount : count ≤ 32)
    (hrep : Limbs.Represents s.memory 2048 count value) :
    Limbs.Represents
      (BigBaseLoop.baseProgressFrom count baseOff start steps s).memory 2048
      count value := by
  induction steps with
  | zero => exact hrep
  | succ steps ih =>
      let before := BigBaseLoop.baseProgressFrom count baseOff start steps s
      let byte := loadedBaseByte before baseOff (start + steps)
      have hbits := bitProgress_preserves_2048 before count byte 8 value
        (by omega) hcount ih
      simpa [BigBaseLoop.baseProgressFrom, before, byte] using hbits

/-! ## Bridging the Horner fold to the calldata bytes -/

theorem loadedBaseByte_toNat (s : State) (baseOff i : Nat) :
    (loadedBaseByte s baseOff i).toNat =
      (YulSemantics.EVM.byteFrom s.executionEnv.calldata.toList
        (baseOff + i)).toNat := by
  have h := congrArg UInt256.toNat
    (Challenge.EvmProof.Bytes.byteAt_zero_readWord s.executionEnv.calldata
      (baseOff + i))
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt
      ((YulSemantics.EVM.byteFrom s.executionEnv.calldata.toList
        (baseOff + i)).toNat_lt.trans (by norm_num : 256 < 2 ^ 256))] at h
  change (UInt256.byteAt ⟨0⟩
    (MachineState.readWord s.executionEnv.calldata (baseOff + i))).toNat = _
  exact h

theorem baseValueAfter_eq (s : State) (modulus baseOff steps : Nat) :
    baseValueAfter s modulus baseOff steps =
      Precompile.bytesToNatPadded s.executionEnv.calldata baseOff steps %
        modulus := by
  unfold baseValueAfter
  induction steps with
  | zero => simp [baseValueSeq]
  | succ steps ih =>
      rw [baseValueSeq, ih, loadedBaseByte_toNat s baseOff (0 + steps),
        Challenge.EvmProof.Bytes.bytesToNatPadded_succ]
      simp [Nat.add_mod, Nat.mul_mod]

theorem baseValueAfter_executionEnv (s t : State)
    (modulus baseOff steps : Nat) (henv : s.executionEnv = t.executionEnv) :
    baseValueAfter s modulus baseOff steps =
      baseValueAfter t modulus baseOff steps := by
  rw [baseValueAfter_eq, baseValueAfter_eq, henv]

/-! ## Preservation across the direct load -/

theorem represents_writeWord_disjoint_region (memory : ByteArray)
    (dst ptr count value word : Nat)
    (hdisjoint : dst + 32 ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word 32) dst)
      ptr count value := by
  refine ⟨hrep.1, ?_⟩
  rw [← hrep.2]
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  have hj' : j < count := by simpa using hj
  apply congrArg UInt256.toNat
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  rcases hdisjoint with hbefore | hafter
  · right
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
    omega
  · left
    omega

theorem loadMemory_preserves_region (calldata : ByteArray) (memory : ByteArray)
    (offset dst length iter ptr count value : Nat) (hiter : iter ≤ length)
    (hlength : length < 2 ^ 256)
    (hdstFit : dst + 32 * Limbs.limbCount length < 2 ^ 256)
    (hdisjoint : dst + 32 * Limbs.limbCount length ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (BigLoad.loadMemory calldata (UInt256.ofNat offset) (UInt256.ofNat length)
        (UInt256.ofNat dst) iter memory)
      ptr count value := by
  have hcount := BigLoadCorrect.loadCount_eq dst length hlength hdstFit
  induction iter with
  | zero => exact hrep
  | succ iter ih =>
      by_cases hguard : iter < BigLoad.loadCount (UInt256.ofNat dst)
          (UInt256.ofNat length)
      · have hlimb : iter < Limbs.limbCount length := by rwa [hcount] at hguard
        have haddr : (BigLoad.loadPtr (UInt256.ofNat dst) iter).toNat =
            dst + 32 * iter :=
          BigLoadCorrect.loadPtr_eq dst length iter hdstFit (by omega)
        have hdisj : dst + 32 * iter + 32 ≤ ptr ∨
            ptr + 32 * count ≤ dst + 32 * iter := by
          rcases hdisjoint with h | h
          · left; omega
          · right; omega
        rw [BigLoad.loadMemory_succ _ _ _ _ _ _ hguard, haddr]
        exact represents_writeWord_disjoint_region _ (dst + 32 * iter) ptr count
          value _ hdisj (ih (by omega))
      · rw [BigLoad.loadMemory_succ_of_ge _ _ _ _ _ _ hguard]
        exact ih (by omega)

theorem setupReturned_base_buffers_zero (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hmBound : m ≤ 1024)
    (hmodOff : modOff < 2 ^ 256) :
    let returned := BigSetup.setupReturned s b e m baseOff expOff modOff
      returnDest rest
    let n := Limbs.limbCount m
    Limbs.Represents returned.memory 1024 n 0 ∧
      Limbs.Represents returned.memory 2048 n 0 := by
  let n := Limbs.limbCount m
  let s0 := BigSetup.afterClear0 s b e m baseOff expOff modOff returnDest rest
  let s1 := BigSetup.afterClear1024 s b e m baseOff expOff modOff returnDest rest
  let s2 := BigSetup.afterClear2048 s b e m baseOff expOff modOff returnDest rest
  let s3 := BigSetup.afterClear6144 s b e m baseOff expOff modOff returnDest rest
  have hn : n ≤ 32 := Limbs.limbCount_le_32 m hmBound
  have hm : m < 2 ^ 256 := by omega
  have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h6144 : (6144 : UInt256) = UInt256.ofNat 6144 := by decide
  have hmNat : (UInt256.ofNat m).toNat = m := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hm]
  have hmodOffNat : (UInt256.ofNat modOff).toNat = modOff := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hmodOff]
  have hz1024s1 : Limbs.Represents s1.memory 1024 n 0 := by
    simpa [s1, BigSetup.afterClear1024, BigHelpers.clearReturned, h1024]
      using BigHelpers.clearMemory_represents_zero s0.memory 1024 n (by omega)
  have hz1024s2 : Limbs.Represents s2.memory 1024 n 0 := by
    simpa [s2, BigSetup.afterClear2048, BigHelpers.clearReturned, h2048] using
      BigHelpers.represents_clearMemory_disjoint_region s1.memory 2048 1024 n
        0 (by omega) (Or.inr (by omega)) hz1024s1
  have hz1024s3 : Limbs.Represents s3.memory 1024 n 0 := by
    simpa [s3, BigSetup.afterClear6144, BigHelpers.clearReturned, h6144] using
      BigHelpers.represents_clearMemory_disjoint_region s2.memory 6144 1024 n
        0 (by omega) (Or.inr (by omega)) hz1024s2
  have hz2048s2 : Limbs.Represents s2.memory 2048 n 0 := by
    simpa [s2, BigSetup.afterClear2048, BigHelpers.clearReturned, h2048]
      using BigHelpers.clearMemory_represents_zero s1.memory 2048 n (by omega)
  have hz2048s3 : Limbs.Represents s3.memory 2048 n 0 := by
    simpa [s3, BigSetup.afterClear6144, BigHelpers.clearReturned, h6144] using
      BigHelpers.represents_clearMemory_disjoint_region s2.memory 6144 2048 n
        0 (by omega) (Or.inr (by omega)) hz2048s2
  have hz1024 := loadMemory_preserves_region s3.executionEnv.calldata
    s3.memory modOff 0 m m 1024 n 0 (by omega) hm (by omega)
    (Or.inl (by omega)) hz1024s3
  have hz2048 := loadMemory_preserves_region s3.executionEnv.calldata
    s3.memory modOff 0 m m 2048 n 0 (by omega) hm (by omega)
    (Or.inl (by omega)) hz2048s3
  exact ⟨by
    simpa [BigSetup.setupReturned, s3, BigLoad.loadReturned,
      BigLoad.loadLoop, h0, hmNat, hmodOffNat, n] using hz1024,
    by simpa [BigSetup.setupReturned, s3, BigLoad.loadReturned,
      BigLoad.loadLoop, h0, hmNat, hmodOffNat, n] using hz2048⟩

/-! ## The state entering the reducing loop -/

theorem baseLoopEntry_initial (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff modulusValue : Nat) (rest : List UInt256)
    (hcountPos : 0 < count) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulusValue) (hbase : baseSize < 2 ^ 256)
    (hoff : baseOff < 2 ^ 256)
    (hzero : Limbs.Represents s.memory 1024 count 0)
    (hzero2048 : Limbs.Represents s.memory 2048 count 0)
    (hmodulus : Limbs.Represents s.memory 0 count modulusValue) :
    let tail := baseTail baseSize e m baseOff rest
    let direct := basePrefix s accumulator count baseSize tail
    let entry := baseLoopEntry s accumulator count baseSize e m baseOff rest
    direct ≤ baseSize ∧
      Limbs.Represents entry.memory 1024 count
        (baseValueAfter s modulusValue baseOff direct) ∧
      Limbs.Represents entry.memory 3072 count 1 ∧
      Limbs.Represents entry.memory 2048 count 0 ∧
      Limbs.Represents entry.memory 0 count modulusValue := by
  let tail := baseTail baseSize e m baseOff rest
  let scanned := BigModulus.scanNonzero s count tail
  let stub := stubbed s count tail
  let cleared := afterClearDouble s accumulator count tail
  let written := baseWritten cleared
  let direct := basePrefix s accumulator count baseSize tail
  let computed := baseDirectOf written count baseSize
  have hdd : direct = directValue written.memory count baseSize := rfl
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  -- the modulus scan and the stub touch no memory
  have hscannedZero : Limbs.Represents stub.memory 1024 count 0 := by
    simpa [stub, stubbed, BigModulus.scanNonzero] using hzero
  have hscannedModulus : Limbs.Represents stub.memory 0 count modulusValue := by
    simpa [stub, stubbed, BigModulus.scanNonzero] using hmodulus
  have hscannedZero2048 : Limbs.Represents stub.memory 2048 count 0 := by
    simpa [stub, stubbed, BigModulus.scanNonzero] using hzero2048
  -- clearLimbs(0x0c00, n)
  have hcleared3072 : Limbs.Represents cleared.memory 3072 count 0 := by
    simpa [cleared, afterClearDouble, BigHelpers.clearReturned, stub, h3072]
      using BigHelpers.clearMemory_represents_zero stub.memory 3072 count
        (by omega)
  have hclearedZero : Limbs.Represents cleared.memory 1024 count 0 := by
    simpa [cleared, afterClearDouble, BigHelpers.clearReturned, stub, h3072]
      using BigHelpers.represents_clearMemory_disjoint_region stub.memory 3072
        1024 count 0 (by omega) (Or.inr (by omega)) hscannedZero
  have hclearedModulus : Limbs.Represents cleared.memory 0 count modulusValue := by
    simpa [cleared, afterClearDouble, BigHelpers.clearReturned, stub, h3072]
      using BigHelpers.represents_clearMemory_disjoint_region stub.memory 3072 0
        count modulusValue (by omega) (Or.inr (by omega)) hscannedModulus
  have hclearedZero2048 : Limbs.Represents cleared.memory 2048 count 0 := by
    simpa [cleared, afterClearDouble, BigHelpers.clearReturned, stub, h3072]
      using BigHelpers.represents_clearMemory_disjoint_region stub.memory 3072
        2048 count 0 (by omega) (Or.inr (by omega)) hscannedZero2048
  -- mstore(0x0c00, 1)
  have hreadZero :
      (MachineState.readWord cleared.memory (3072 + 32 * 0)).toNat = 0 :=
    represents_zero_read cleared.memory 3072 count 0 (by omega) hcleared3072
  have hvalue := BigLoadCorrect.value_memoryLimbs_write_add cleared.memory 3072
    count 0 1 hcountPos (by rw [hreadZero]; norm_num)
  have hclearedValue := Limbs.value_of_represents hcleared3072
  rw [hclearedValue, Nat.zero_add, Nat.pow_zero, Nat.mul_one] at hvalue
  have hwrittenOne : Limbs.Represents written.memory 3072 count 1 := by
    have : Limbs.Represents (MachineState.writeBytes cleared.memory
        (Data.Bytes.natToBytesPadded 1 32) 3072) 3072 count 1 := by
      apply (Limbs.represents_iff_value (by
        exact Nat.one_lt_pow (by omega) Limbs.radix_gt_one)).2
      simpa [hreadZero] using hvalue
    simpa [written, baseWritten] using this
  have hwrittenZero : Limbs.Represents written.memory 1024 count 0 := by
    simpa [written, baseWritten] using
      represents_writeWord_disjoint_region cleared.memory 3072 1024 count
        0 1 (Or.inr (by omega)) hclearedZero
  have hwrittenModulus : Limbs.Represents written.memory 0 count modulusValue := by
    simpa [written, baseWritten] using
      represents_writeWord_disjoint_region cleared.memory 3072 0 count
        modulusValue 1 (Or.inr (by omega)) hclearedModulus
  have hwrittenZero2048 : Limbs.Represents written.memory 2048 count 0 := by
    simpa [written, baseWritten] using
      represents_writeWord_disjoint_region cleared.memory 3072 2048 count
        0 1 (Or.inr (by omega)) hclearedZero2048
  -- the prefix length is bounded and its value is already a residue
  have hdirectLe : direct ≤ baseSize := by
    rw [hdd]; exact directValue_le _ count baseSize
  have hlimbLe : Limbs.limbCount direct ≤ count := by
    rw [hdd]
    exact limbCount_directValue_le written.memory count baseSize hcountPos hcount
  have hdirectMod : direct % 2 ^ 256 = direct := Nat.mod_eq_of_lt (by omega)
  have hbaseOffMod : baseOff % 2 ^ 256 = baseOff := Nat.mod_eq_of_lt hoff
  have hprefixLt : Precompile.bytesToNatPadded written.executionEnv.calldata
      baseOff direct < modulusValue := by
    have h1 := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
      written.executionEnv.calldata baseOff direct
    have h2 : (256 : Nat) ^ direct ≤ modulusValue := by
      rw [hdd]
      exact pow_directValue_le written.memory count baseSize modulusValue
        hcountPos hcount hmodulusPos hwrittenModulus
    omega
  -- run the certified loadBigEndian
  have hzeroPrefix : Limbs.Represents computed.memory 1024
      (Limbs.limbCount direct) 0 := by
    have : Limbs.Represents written.memory 1024 (Limbs.limbCount direct) 0 :=
      represents_zero_truncate written.memory 1024 (Limbs.limbCount direct)
        count hlimbLe hwrittenZero
    simpa [computed, baseDirectOf] using this
  have hloaded := BigLoadCorrect.loadReturned_represents computed baseOff 1024
    direct (UInt256.ofNat 1677)
    (UInt256.ofNat direct :: frame accumulator count tail) hoff (by omega)
    (by
      have : Limbs.limbCount direct ≤ 32 := by omega
      omega)
    hzeroPrefix
  -- extend the loaded prefix to the full limb count
  have hhigh : ∀ i, i < count - Limbs.limbCount direct →
      (MachineState.readWord
        (BigLoad.loadReturned computed (UInt256.ofNat baseOff)
          (UInt256.ofNat direct) (UInt256.ofNat 1024) (UInt256.ofNat 1677)
          (UInt256.ofNat direct :: frame accumulator count tail)).memory
        (1024 + 32 * (Limbs.limbCount direct + i))).toNat = 0 := by
    intro i hi
    have hsingle : Limbs.Represents computed.memory
        (1024 + 32 * (Limbs.limbCount direct + i)) 1 0 := by
      apply represents_zero_of_reads
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      have := represents_zero_read written.memory 1024 count
        (Limbs.limbCount direct + i) (by omega) hwrittenZero
      simpa [computed, baseDirectOf] using this
    have hpres := loadMemory_preserves_region computed.executionEnv.calldata
      computed.memory baseOff 1024 direct direct
      (1024 + 32 * (Limbs.limbCount direct + i)) 1 0 (by omega) (by omega)
      (by
        have : Limbs.limbCount direct ≤ 32 := by omega
        omega)
      (Or.inl (by omega)) hsingle
    have hbaseOffNat : (UInt256.ofNat baseOff).toNat = baseOff := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
    have hdirectNat : (UInt256.ofNat direct).toNat = direct := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have := represents_zero_read _ (1024 + 32 * (Limbs.limbCount direct + i)) 1 0
      (by omega) hpres
    simpa [BigLoad.loadReturned, BigLoad.loadLoop, hbaseOffNat, hdirectNat,
      hbaseOffMod, hdirectMod] using this
  have hentryBase : Limbs.Represents
      (baseLoopEntry s accumulator count baseSize e m baseOff rest).memory 1024
      count (Precompile.bytesToNatPadded written.executionEnv.calldata baseOff
        direct) := by
    have hsplit : Limbs.limbCount direct + (count - Limbs.limbCount direct)
        = count := by omega
    have hcalldata : computed.executionEnv.calldata =
        written.executionEnv.calldata := by
      simp [computed, baseDirectOf]
    have hext := represents_extend
      (BigLoad.loadReturned computed (UInt256.ofNat baseOff)
        (UInt256.ofNat direct) (UInt256.ofNat 1024) (UInt256.ofNat 1677)
        (UInt256.ofNat direct :: frame accumulator count tail)).memory
      1024 (Limbs.limbCount direct) (count - Limbs.limbCount direct)
      (Precompile.bytesToNatPadded computed.executionEnv.calldata baseOff direct)
      (by
        rw [hsplit]
        have h1 := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
          computed.executionEnv.calldata baseOff direct
        have h2 : (256 : Nat) ^ direct ≤ Limbs.radix ^ count := by
          rw [Limbs.pow_radix]
          exact Nat.pow_le_pow_right (by omega) (by
            have := Limbs.width_le_limbs direct
            omega)
        omega)
      hloaded hhigh
    rw [hsplit] at hext
    rw [hcalldata] at hext
    simpa [baseLoopEntry, computed, written, cleared, tail, direct] using hext
  have hentryOne : Limbs.Represents
      (baseLoopEntry s accumulator count baseSize e m baseOff rest).memory 3072
      count 1 := by
    have hpres := loadMemory_preserves_region computed.executionEnv.calldata
      computed.memory baseOff 1024 direct direct 3072 count 1 (by omega)
      (by omega)
      (by
        have : Limbs.limbCount direct ≤ 32 := by omega
        omega)
      (Or.inl (by
        have : Limbs.limbCount direct ≤ 32 := by omega
        omega))
      (by simpa [computed, baseDirectOf] using hwrittenOne)
    have hbaseOffNat : (UInt256.ofNat baseOff).toNat = baseOff := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
    have hdirectNat : (UInt256.ofNat direct).toNat = direct := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simpa [baseLoopEntry, computed, written, cleared, tail, direct,
      BigLoad.loadReturned, BigLoad.loadLoop, hbaseOffNat, hdirectNat,
      hbaseOffMod, hdirectMod]
      using hpres
  have hentry2048 : Limbs.Represents
      (baseLoopEntry s accumulator count baseSize e m baseOff rest).memory 2048
      count 0 := by
    have hpres := loadMemory_preserves_region computed.executionEnv.calldata
      computed.memory baseOff 1024 direct direct 2048 count 0 (by omega)
      (by omega)
      (by
        have : Limbs.limbCount direct ≤ 32 := by omega
        omega)
      (Or.inl (by
        have : Limbs.limbCount direct ≤ 32 := by omega
        omega))
      (by simpa [computed, baseDirectOf] using hwrittenZero2048)
    have hbaseOffNat : (UInt256.ofNat baseOff).toNat = baseOff := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
    have hdirectNat : (UInt256.ofNat direct).toNat = direct := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simpa [baseLoopEntry, computed, written, cleared, tail, direct,
      BigLoad.loadReturned, BigLoad.loadLoop, hbaseOffNat, hdirectNat,
      hbaseOffMod, hdirectMod]
      using hpres
  have hentryModulus : Limbs.Represents
      (baseLoopEntry s accumulator count baseSize e m baseOff rest).memory 0
      count modulusValue := by
    have hpres := loadMemory_preserves_region computed.executionEnv.calldata
      computed.memory baseOff 1024 direct direct 0 count modulusValue
      (by omega) (by omega)
      (by
        have : Limbs.limbCount direct ≤ 32 := by omega
        omega)
      (Or.inr (by omega))
      (by simpa [computed, baseDirectOf] using hwrittenModulus)
    have hbaseOffNat : (UInt256.ofNat baseOff).toNat = baseOff := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
    have hdirectNat : (UInt256.ofNat direct).toNat = direct := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simpa [baseLoopEntry, computed, written, cleared, tail, direct,
      BigLoad.loadReturned, BigLoad.loadLoop, hbaseOffNat, hdirectNat,
      hbaseOffMod, hdirectMod]
      using hpres
  -- the loaded prefix already equals the Horner value after `direct` bytes
  have henvWritten : written.executionEnv = s.executionEnv := by
    simp [written, baseWritten, cleared, afterClearDouble,
      BigHelpers.clearReturned, stub, stubbed, BigModulus.scanNonzero]
  have hvalueEq : baseValueAfter s modulusValue baseOff direct =
      Precompile.bytesToNatPadded written.executionEnv.calldata baseOff direct := by
    rw [baseValueAfter_eq, henvWritten, Nat.mod_eq_of_lt (by
      rw [henvWritten] at hprefixLt
      exact hprefixLt)]
  refine ⟨hdirectLe, ?_, hentryOne, hentry2048, hentryModulus⟩
  rw [hvalueEq]
  exact hentryBase


theorem baseValueSeq_executionEnv (s t : State)
    (modulus baseOff start acc steps : Nat)
    (henv : s.executionEnv = t.executionEnv) :
    baseValueSeq s modulus baseOff start acc steps =
      baseValueSeq t modulus baseOff start acc steps := by
  have hbyte : ∀ i, loadedBaseByte s baseOff i = loadedBaseByte t baseOff i := by
    intro i
    unfold loadedBaseByte
    rw [henv]
  induction steps with
  | zero => rfl
  | succ steps ih => rw [baseValueSeq, baseValueSeq, ih, hbyte]

/-! ## The state entering the exponent phase -/

theorem initialAccumulator_represents (entry : State) (accumulator : UInt256)
    (count baseSize baseOff direct prefixValue modulusValue : Nat)
    (tail : List UInt256) (hcountPos : 0 < count) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulusValue) (hprefix : prefixValue < modulusValue)
    (hbase : Limbs.Represents entry.memory 1024 count prefixValue)
    (hone : Limbs.Represents entry.memory 3072 count 1)
    (hzero2048 : Limbs.Represents entry.memory 2048 count 0)
    (hmodulus : Limbs.Represents entry.memory 0 count modulusValue) :
    let returned := BigBaseLoop.initialAccumulator entry accumulator count
      baseSize baseOff direct tail
    Limbs.Represents returned.memory 2048 count (1 % modulusValue) ∧
      Limbs.Represents returned.memory 1024 count
        (baseValueSeq entry modulusValue baseOff direct prefixValue
          (baseSize - direct)) ∧
      Limbs.Represents returned.memory 0 count modulusValue := by
  let progress := BigBaseLoop.baseProgressFrom count baseOff direct
    (baseSize - direct) entry
  let baseValue := baseValueSeq entry modulusValue baseOff direct prefixValue
    (baseSize - direct)
  let exit := BigBaseLoop.convertedExit entry accumulator count baseSize baseOff
    direct tail
  let helperRest := [accumulator, UInt256.ofNat count,
    UInt256.ofNat baseSize] ++ tail
  have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have h944 : (944 : UInt256) = UInt256.ofNat 944 := by decide
  have hprogress := baseProgressFrom_represents entry count baseOff direct
    (baseSize - direct) modulusValue prefixValue hcount hmodulusPos hprefix
    hbase hone hmodulus
  have hprogressZero := baseProgressFrom_preserves_2048 entry count baseOff
    direct (baseSize - direct) 0 hcount hzero2048
  have hexitBase : Limbs.Represents exit.memory 1024 count baseValue := by
    simpa [exit, BigBaseLoop.convertedExit, BigBase.outerExit,
      BigBase.outerLoop, progress, baseValue] using hprogress.1
  have hexitOne : Limbs.Represents exit.memory 3072 count 1 := by
    simpa [exit, BigBaseLoop.convertedExit, BigBase.outerExit,
      BigBase.outerLoop, progress] using hprogress.2.1
  have hexitZero : Limbs.Represents exit.memory 2048 count 0 := by
    simpa [exit, BigBaseLoop.convertedExit, BigBase.outerExit,
      BigBase.outerLoop, progress] using hprogressZero
  have hexitModulus : Limbs.Represents exit.memory 0 count modulusValue := by
    simpa [exit, BigBaseLoop.convertedExit, BigBase.outerExit,
      BigBase.outerLoop, progress] using hprogress.2.2
  have hacc : Limbs.Represents
      (BigBaseLoop.initialAccumulator entry accumulator count baseSize baseOff
        direct tail).memory 2048 count (1 % modulusValue) := by
    simpa [BigBaseLoop.initialAccumulator, helperRest, exit, h0, h1, h2048,
      h3072, h944] using
      BigHelpers.addReturned_represents_mod exit 2048 3072 0 count 1 0 1
        modulusValue (UInt256.ofNat 944) helperRest (by omega) (by omega)
        (by omega) (by omega) (by omega) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        hexitZero hexitOne hexitModulus (by omega) (by omega) hexitModulus.1
  have hbaseRep : Limbs.Represents
      (BigBaseLoop.initialAccumulator entry accumulator count baseSize baseOff
        direct tail).memory 1024 count baseValue := by
    simpa [BigBaseLoop.initialAccumulator, helperRest, exit, h0, h1, h2048,
      h3072, h944] using
      BigHelpers.addReturned_preserves_region exit 2048 3072 1 0 1024 count
        baseValue (UInt256.ofNat 944) helperRest (by omega) (by omega)
        (Or.inr (by omega)) (Or.inl (by omega)) hexitBase
  have hmod : Limbs.Represents
      (BigBaseLoop.initialAccumulator entry accumulator count baseSize baseOff
        direct tail).memory 0 count modulusValue := by
    simpa [BigBaseLoop.initialAccumulator, helperRest, exit, h0, h1, h2048,
      h3072, h944] using
      BigHelpers.addReturned_preserves_region exit 2048 3072 1 0 0 count
        modulusValue (UInt256.ofNat 944) helperRest (by omega) (by omega)
        (Or.inr (by omega)) (Or.inl (by omega)) hexitModulus
  exact ⟨hacc, by simpa [baseValue] using hbaseRep, hmod⟩

theorem exponentState_initial (input : ByteArray) (returnDest : UInt256)
    (rest : List UInt256) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (hmodulusPos : 0 < Word.modulusValue input) :
    let b := baseSize input
    let e := exponentSize input
    let m := modulusSize input
    let expOff := Word.expOffset input
    let modOff := Word.modulusOffset input
    let entry := BigComplete.exponentState (Main.headerState input) b e m 96
      expOff modOff returnDest rest
    Limbs.Represents entry.memory 2048 (Limbs.limbCount m)
        (1 % Word.modulusValue input) ∧
      Limbs.Represents entry.memory 1024 (Limbs.limbCount m)
        (BitPrefix.baseNat input % Word.modulusValue input) ∧
      Limbs.Represents entry.memory 0 (Limbs.limbCount m)
        (Word.modulusValue input) := by
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := Word.expOffset input
  let modOff := Word.modulusOffset input
  let n := Limbs.limbCount m
  let header := Main.headerState input
  let loaded := BigComplete.setupState header b e m 96 expOff modOff returnDest
    rest
  let accumulator := BigComplete.modulusOr header b e m 96 expOff modOff
    returnDest rest
  let baseTailList := BigComplete.baseRest expOff modOff returnDest rest
  let direct := BigComplete.basePrefixLen header b e m 96 expOff modOff
    returnDest rest
  let base := BigComplete.baseState header b e m 96 expOff modOff returnDest
    rest
  have hb : b ≤ 1024 := by simpa [b] using hvalid.2.1
  have hm : m ≤ 1024 := by simpa [m] using hvalid.2.2.2
  have hn : n ≤ 32 := Limbs.limbCount_le_32 m hm
  have hnPos : 0 < n := Limbs.limbCount_pos (by simp [m]; omega)
  have hmodOff : modOff < 2 ^ 256 := by
    rcases hvalid with ⟨_, hb', he', _⟩
    simp only [modOff, Word.modulusOffset, Word.expOffset]
    omega
  have hmodulus : Limbs.Represents loaded.memory 0 n
      (Word.modulusValue input) := by
    have hraw := BigSetup.setupReturned_modulus_represents header b e m 96
      expOff modOff returnDest rest hm hmodOff
    rw [show header.executionEnv.calldata = input by rfl] at hraw
    simpa [loaded, BigComplete.setupState, header, b, e, m, n, expOff,
      modOff, Word.modulusValue, Word.modulusOffset] using hraw
  have hzeros := setupReturned_base_buffers_zero header b e m 96 expOff modOff
    returnDest rest hm hmodOff
  have hentry := baseLoopEntry_initial loaded accumulator n b e m 96
    (Word.modulusValue input) baseTailList hnPos hn hmodulusPos (by omega)
    (by norm_num) hzeros.1 hzeros.2 hmodulus
  have hdirectEq : direct = BigBase.basePrefix loaded accumulator n b
      (BigBase.baseTail b e m 96 baseTailList) := by
    rfl
  have hbaseEq : base = BigBase.baseLoopEntry loaded accumulator n b e m 96
      baseTailList := by
    rfl
  have hprefixLt : baseValueAfter loaded (Word.modulusValue input) 96 direct <
      Word.modulusValue input :=
    baseValueAfter_lt loaded (Word.modulusValue input) 96 direct hmodulusPos
  have hbaseEnv : base.executionEnv = loaded.executionEnv := by
    simp [hbaseEq, BigBase.baseLoopEntry, BigLoad.loadReturned,
      BigLoad.loadLoop, BigBase.baseDirectOf, BigBase.baseWritten,
      BigBase.afterClearDouble, BigHelpers.clearReturned, BigBase.stubbed,
      BigModulus.scanNonzero]
  have hresult := initialAccumulator_represents base accumulator n b 96 direct
    (baseValueAfter loaded (Word.modulusValue input) 96 direct)
    (Word.modulusValue input)
    ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat 96] ++ baseTailList)
    hnPos hn hmodulusPos hprefixLt
    (by rw [hbaseEq, hdirectEq]; exact hentry.2.1)
    (by rw [hbaseEq]; exact hentry.2.2.1)
    (by rw [hbaseEq]; exact hentry.2.2.2.1)
    (by rw [hbaseEq]; exact hentry.2.2.2.2)
  have hshift : baseValueSeq base (Word.modulusValue input) 96 direct
      (baseValueAfter loaded (Word.modulusValue input) 96 direct)
      (b - direct) = BitPrefix.baseNat input % Word.modulusValue input := by
    rw [baseValueSeq_executionEnv base loaded _ _ _ _ _ hbaseEnv]
    have hsplit := baseValueSeq_shift loaded (Word.modulusValue input) 96
      direct 0 (b - direct)
    have hdirectLe : direct ≤ b := by
      have := hentry.1
      rw [hdirectEq]
      exact this
    rw [show baseValueAfter loaded (Word.modulusValue input) 96 direct =
      baseValueSeq loaded (Word.modulusValue input) 96 0 0 direct from rfl,
      hsplit, show direct + (b - direct) = b by omega]
    change baseValueAfter loaded (Word.modulusValue input) 96 b = _
    rw [baseValueAfter_eq]
    rfl
  rw [hshift] at hresult
  simpa [BigComplete.exponentState, BigComplete.limbCount, base, accumulator,
    direct, n, b, e, m, expOff, modOff, baseTailList, header, loaded]
    using hresult

end Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseCorrect
