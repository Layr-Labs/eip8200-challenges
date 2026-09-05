import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentScanGas
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Functional correctness of leading-zero exponent skipping -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentScanCorrect

open EvmSemantics
open EvmSemantics.EVM
open BigExponent
open BigExponentScan
open BigExponentScanGas

theorem oneMod_pow (modulus N : Nat) :
    (1 % modulus) ^ N % modulus = 1 % modulus := by
  rw [← Nat.pow_mod, Nat.one_pow]

theorem natBitAfter_of_zero_prefix (modulus : Nat) (byte : UInt256)
    (base j0 : Nat) (hmodulusPos : 0 < modulus)
    (hz : ∀ t, t < j0 → WordCorrect.exponentBitNat byte t = 0) :
    WordCorrect.natBitAfter modulus byte base j0 (1 % modulus) =
      1 % modulus := by
  have hacc : 1 % modulus < modulus := Nat.mod_lt _ hmodulusPos
  rw [WordCorrect.natBitAfter_eq modulus byte base (1 % modulus) j0 hacc,
    bitPrefix_eq_zero byte j0 hz, Nat.pow_zero, Nat.mul_one,
    oneMod_pow]

theorem natExpStep_of_zero_byte (modulus : Nat) (byte : UInt256) (base : Nat)
    (hmodulusPos : 0 < modulus) (hbyte : byte.toNat = 0) :
    WordCorrect.natExpStep modulus byte (1 % modulus) base =
      1 % modulus := by
  have hacc : 1 % modulus < modulus := Nat.mod_lt _ hmodulusPos
  have hlt : byte.toNat < 256 := by omega
  rw [← BigExponentCorrect.natBitAfter_eight_eq_natExpStep modulus byte
      (1 % modulus) base hacc hlt,
    WordCorrect.natBitAfter_eq modulus byte base (1 % modulus) 8 hacc,
    WordCorrect.bitPrefix_eight byte hlt, hbyte, Nat.pow_zero, Nat.mul_one,
    oneMod_pow]

theorem exponentValueAfter_of_zero_prefix (s : State)
    (modulus base expOff k : Nat) (hmodulusPos : 0 < modulus)
    (hz : ∀ t, t < k → (loadedExponentByte s expOff t).toNat = 0) :
    BigExponentCorrect.exponentValueAfter s modulus base expOff k
      (1 % modulus) = 1 % modulus := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [BigExponentCorrect.exponentValueAfter,
        ih (fun t ht => hz t (by omega))]
      exact natExpStep_of_zero_byte modulus (loadedExponentByte s expOff k)
        base hmodulusPos (hz k (by omega))

def natBitFrom (modulus : Nat) (byte : UInt256) (base start acc : Nat) :
    Nat → Nat
  | 0 => acc
  | t + 1 =>
      WordCorrect.natBitStep modulus byte (start + t)
        (natBitFrom modulus byte base start acc t) base

theorem natBitFrom_lt (modulus : Nat) (byte : UInt256)
    (base start acc t : Nat) (hmodulusPos : 0 < modulus)
    (hacc : acc < modulus) :
    natBitFrom modulus byte base start acc t < modulus := by
  induction t with
  | zero => exact hacc
  | succ t _ =>
      rw [natBitFrom]
      exact WordCorrect.natBitStep_lt modulus byte (start + t) _ base
        hmodulusPos

theorem natBitAfter_split (modulus : Nat) (byte : UInt256)
    (base a t acc : Nat) :
    WordCorrect.natBitAfter modulus byte base (a + t) acc =
      natBitFrom modulus byte base a
        (WordCorrect.natBitAfter modulus byte base a acc) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [show a + (t + 1) = (a + t) + 1 from by omega,
        WordCorrect.natBitAfter, ih, natBitFrom]

def expValueFrom (s : State) (modulus base expOff start acc : Nat) :
    Nat → Nat
  | 0 => acc
  | t + 1 =>
      WordCorrect.natExpStep modulus
        (loadedExponentByte s expOff (start + t))
        (expValueFrom s modulus base expOff start acc t) base

theorem expValueFrom_lt (s : State) (modulus base expOff start acc t : Nat)
    (hmodulusPos : 0 < modulus) (hacc : acc < modulus) :
    expValueFrom s modulus base expOff start acc t < modulus := by
  induction t with
  | zero => exact hacc
  | succ t _ =>
      rw [expValueFrom, WordCorrect.natExpStep]
      exact Nat.mod_lt _ hmodulusPos

theorem expValueFrom_executionEnv (s t : State)
    (modulus base expOff start acc steps : Nat)
    (henv : s.executionEnv = t.executionEnv) :
    expValueFrom s modulus base expOff start acc steps =
      expValueFrom t modulus base expOff start acc steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hbyte : loadedExponentByte s expOff (start + steps) =
          loadedExponentByte t expOff (start + steps) := by
        unfold loadedExponentByte
        rw [henv]
      rw [expValueFrom, expValueFrom, ih, hbyte]

theorem exponentValueAfter_split (s : State)
    (modulus base expOff a t acc : Nat) :
    BigExponentCorrect.exponentValueAfter s modulus base expOff (a + t) acc =
      expValueFrom s modulus base expOff a
        (BigExponentCorrect.exponentValueAfter s modulus base expOff a acc)
        t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [show a + (t + 1) = (a + t) + 1 from by omega,
        BigExponentCorrect.exponentValueAfter, ih, expValueFrom]

theorem exponentBitProgressFrom_represents (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i : Nat)
    (offset byte : UInt256) (rest : List UInt256)
    (start steps acc base modulus : Nat) (hsteps : start + steps ≤ 8)
    (hcount : count ≤ 32) (hmodulusPos : 0 < modulus)
    (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := exponentBitProgressFrom s accumulatorWord count b e m
      baseOff expOff i start offset byte rest steps
    Limbs.Represents progress.memory 2048 count
        (natBitFrom modulus byte base start acc steps) ∧
      Limbs.Represents progress.memory 1024 count base ∧
      Limbs.Represents progress.memory 0 count modulus := by
  induction steps with
  | zero => exact ⟨hacc, hbase, hmodulus⟩
  | succ steps ih =>
      let before := exponentBitProgressFrom s accumulatorWord count b e m
        baseOff expOff i start offset byte rest steps
      let beforeValue := natBitFrom modulus byte base start acc steps
      have hbefore := ih (by omega)
      have hbeforeReduced : beforeValue < modulus :=
        natBitFrom_lt modulus byte base start acc steps hmodulusPos haccReduced
      have hstep := BigExponentCorrect.selectProgress_represents_bitStep before
        accumulatorWord count b e m baseOff expOff i (start + steps) offset byte
        rest beforeValue base modulus hcount hmodulusPos hbeforeReduced
        hbefore.1 hbefore.2.1 hbefore.2.2
      simpa [exponentBitProgressFrom, before, beforeValue, natBitFrom,
        BigExponentCorrect.bitStepValue_eq_natBitStep modulus byte
          (start + steps) beforeValue base (by omega)] using hstep

theorem exponentByteProgressFrom_represents (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) (start steps acc base modulus : Nat)
    (hcount : count ≤ 32) (hmodulusPos : 0 < modulus)
    (haccReduced : acc < modulus)
    (hacc : Limbs.Represents s.memory 2048 count acc)
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    let progress := exponentByteProgressFrom s accumulatorWord count b e m
      baseOff expOff start rest steps
    Limbs.Represents progress.memory 2048 count
        (expValueFrom s modulus base expOff start acc steps) ∧
      Limbs.Represents progress.memory 1024 count base ∧
      Limbs.Represents progress.memory 0 count modulus := by
  induction steps with
  | zero => exact ⟨hacc, hbase, hmodulus⟩
  | succ steps ih =>
      let before := exponentByteProgressFrom s accumulatorWord count b e m
        baseOff expOff start rest steps
      let beforeValue := expValueFrom s modulus base expOff start acc steps
      let offset := UInt256.ofNat (expOff + (start + steps))
      let byte := loadedExponentByte before expOff (start + steps)
      have hbefore := ih
      have hbeforeReduced : beforeValue < modulus :=
        expValueFrom_lt s modulus base expOff start acc steps hmodulusPos
          haccReduced
      have hbyteEnv : before.executionEnv = s.executionEnv :=
        exponentByteProgressFrom_executionEnv s accumulatorWord count b e m
          baseOff expOff start steps rest
      have hbyte : byte = loadedExponentByte s expOff (start + steps) := by
        simp only [byte, loadedExponentByte]
        rw [hbyteEnv]
      have hbits := BigExponentCorrect.exponentBitProgress_represents before
        accumulatorWord count b e m baseOff expOff (start + steps) offset byte
        rest 8 beforeValue base modulus (by omega) hcount hmodulusPos
        hbeforeReduced hbefore.1 hbefore.2.1 hbefore.2.2
      have hbyteLt : byte.toNat < 256 := by
        rw [hbyte]
        exact BigExponentCorrect.loadedExponentByte_lt s expOff (start + steps)
      have hstepEq := BigExponentCorrect.natBitAfter_eight_eq_natExpStep
        modulus byte beforeValue base hbeforeReduced hbyteLt
      rw [hstepEq] at hbits
      simpa [exponentByteProgressFrom, before, beforeValue, offset, byte,
        expValueFrom, hbyte] using hbits

theorem exponentPhase_represents (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (base modulus : Nat) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulus) (_hbaseReduced : base < modulus)
    (hacc : Limbs.Represents s.memory 2048 count (1 % modulus))
    (hbase : Limbs.Represents s.memory 1024 count base)
    (hmodulus : Limbs.Represents s.memory 0 count modulus) :
    Limbs.Represents
      (exponentPhaseState s accumulatorWord count b e m baseOff expOff
        rest).memory 2048 count
      (BigExponentCorrect.exponentValueAfter s modulus base expOff e
        (1 % modulus)) := by
  let i := coldByteIndex s expOff e
  have hiLe : i ≤ e := coldByteIndex_le s expOff e
  by_cases hiEq : i = e
  · have hval : BigExponentCorrect.exponentValueAfter s modulus base expOff e
        (1 % modulus) = 1 % modulus :=
      exponentValueAfter_of_zero_prefix s modulus base expOff e hmodulusPos
        (fun t ht => coldByteIndex_zeros s expOff e t
          (by simpa [i, hiEq] using ht))
    rw [hval]
    simpa [exponentPhaseState, i, hiEq] using hacc
  · have hi : i < e := by omega
    let byte := loadedByte s expOff i
    let j := coldBitIndex byte
    have hbyte : byte.toNat ≠ 0 := by
      simpa [byte, i] using coldByteIndex_hit s expOff e hi
    have hj : j < 8 := coldBitIndex_lt byte (loadedByte_lt256 s expOff i) hbyte
    have hprefix : BigExponentCorrect.exponentValueAfter s modulus base expOff
        i (1 % modulus) = 1 % modulus :=
      exponentValueAfter_of_zero_prefix s modulus base expOff i hmodulusPos
        (fun t ht => coldByteIndex_zeros s expOff e t
          (by simpa [i] using ht))
    have hzeroBits : ∀ t, t < j → WordCorrect.exponentBitNat byte t = 0 := by
      intro t ht
      rw [← exponentBit_toNat_eq_bitNat byte t (by omega)]
      exact coldBitIndex_zeros byte t ht
    have hbitPrefix := natBitAfter_of_zero_prefix modulus byte base j
      hmodulusPos hzeroBits
    have hbitsRep := exponentBitProgressFrom_represents s accumulatorWord count
      b e m baseOff expOff i (loadedOffset expOff i) byte rest j (8 - j)
      (WordCorrect.natBitAfter modulus byte base j (1 % modulus)) base modulus
      (by omega) hcount hmodulusPos
      (WordCorrect.natBitAfter_lt modulus byte base (1 % modulus) j
        hmodulusPos (Nat.mod_lt _ hmodulusPos))
      (by simpa [hbitPrefix] using hacc) hbase hmodulus
    have hsplit : natBitFrom modulus byte base j
        (WordCorrect.natBitAfter modulus byte base j (1 % modulus)) (8 - j) =
        WordCorrect.natBitAfter modulus byte base 8 (1 % modulus) := by
      rw [← natBitAfter_split]
      congr 2
      omega
    have hbyteVal : BigExponentCorrect.exponentValueAfter s modulus base expOff
        (i + 1) (1 % modulus) =
        WordCorrect.natBitAfter modulus byte base 8 (1 % modulus) := by
      rw [BigExponentCorrect.natBitAfter_eight_eq_natExpStep modulus byte
          (1 % modulus) base (Nat.mod_lt _ hmodulusPos)
          (loadedByte_lt256 s expOff i),
        BigExponentCorrect.exponentValueAfter, hprefix]
      rfl
    let first := firstByteProgress s accumulatorWord count b e m baseOff
      expOff i j rest
    have hbytesRep := exponentByteProgressFrom_represents first accumulatorWord
      count b e m baseOff expOff rest (i + 1) (e - (i + 1))
      (BigExponentCorrect.exponentValueAfter s modulus base expOff (i + 1)
        (1 % modulus)) base modulus hcount hmodulusPos
      (BigExponentCorrect.exponentValueAfter_lt s modulus base expOff _
        (1 % modulus) hmodulusPos (Nat.mod_lt _ hmodulusPos))
      (by rw [hbyteVal, ← hsplit]
          simpa [first, firstByteProgress, byte] using hbitsRep.1)
      (by simpa [first, firstByteProgress, byte] using hbitsRep.2.1)
      (by simpa [first, firstByteProgress, byte] using hbitsRep.2.2)
    have henv : first.executionEnv = s.executionEnv := by
      simp [first, firstByteProgress]
    have htail : BigExponentCorrect.exponentValueAfter s modulus base expOff e
        (1 % modulus) =
        expValueFrom first modulus base expOff (i + 1)
          (BigExponentCorrect.exponentValueAfter s modulus base expOff (i + 1)
            (1 % modulus)) (e - (i + 1)) := by
      rw [expValueFrom_executionEnv first s _ _ _ _ _ _ henv,
        ← exponentValueAfter_split]
      congr 3
      omega
    rw [htail]
    simpa [exponentPhaseState, i, hiEq, foundProgress, first, byte, j] using
      hbytesRep.1

end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentScanCorrect
