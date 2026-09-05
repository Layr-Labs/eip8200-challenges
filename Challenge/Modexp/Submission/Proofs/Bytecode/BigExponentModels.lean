import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Pure progress models for multi-limb exponentiation -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent

open EvmSemantics
open EvmSemantics.EVM

def exponentBitProgress (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => s
  | j + 1 =>
      bitStepProgress
        (exponentBitProgress s accumulatorWord count b e m baseOff expOff i
          offset byte rest j)
        accumulatorWord count b e m baseOff expOff i j offset byte rest

@[simp] theorem exponentBitProgress_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (exponentBitProgress s accumulatorWord count b e m baseOff expOff i offset
      byte rest j).executionEnv = s.executionEnv := by
  induction j with
  | zero => rfl
  | succ j ih => simp [exponentBitProgress, ih]

@[simp] theorem exponentBitProgress_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (exponentBitProgress s accumulatorWord count b e m baseOff expOff i offset
      byte rest j).halt = s.halt := by
  induction j with
  | zero => rfl
  | succ j ih => simp [exponentBitProgress, ih]

def exponentBitLoopState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  innerLoop
    (exponentBitProgress s accumulatorWord count b e m baseOff expOff i offset
      byte rest j)
    accumulatorWord count b e m baseOff expOff i offset byte rest j


def afterExponentByte (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  outerLoop
    (exponentBitProgress s accumulatorWord count b e m baseOff expOff i offset
      byte rest 8)
    accumulatorWord count b e m baseOff expOff rest (i + 1)


def exponentByteProgress (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : Nat → State
  | 0 => s
  | i + 1 =>
      let before := exponentByteProgress s accumulatorWord count b e m baseOff
        expOff rest i
      let offset := UInt256.ofNat (expOff + i)
      let byte := loadedExponentByte before expOff i
      exponentBitProgress before accumulatorWord count b e m baseOff expOff i
        offset byte rest 8

@[simp] theorem exponentByteProgress_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i : Nat)
    (rest : List UInt256) :
    (exponentByteProgress s accumulatorWord count b e m baseOff expOff rest
      i).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih => simp [exponentByteProgress, ih]

@[simp] theorem exponentByteProgress_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i : Nat)
    (rest : List UInt256) :
    (exponentByteProgress s accumulatorWord count b e m baseOff expOff rest
      i).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih => simp [exponentByteProgress, ih]

def exponentOuterState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  outerLoop
    (exponentByteProgress s accumulatorWord count b e m baseOff expOff rest i)
    accumulatorWord count b e m baseOff expOff rest i


section ColdPath
set_option linter.unusedVariables false


/-- Index of the first nonzero exponent byte at or after `i`, bounded by `fuel`. -/
def coldScan (s : State) (expOff : Nat) : Nat → Nat → Nat
  | i, 0 => i
  | i, fuel + 1 =>
      if (loadedExponentByte s expOff i).toNat = 0 then
        coldScan s expOff (i + 1) fuel
      else i

/-- Index of the first nonzero exponent byte, or `e` if the exponent is zero. -/
def coldByteIndex (s : State) (expOff e : Nat) : Nat := coldScan s expOff 0 e

/-- Index of the first set bit of `byte` at or after `j`, bounded by `fuel`. -/
def coldBitScan (byte : UInt256) : Nat → Nat → Nat
  | j, 0 => j
  | j, fuel + 1 =>
      if (exponentBit byte j).toNat = 0 then coldBitScan byte (j + 1) fuel else j

/-- Index of the first set bit of `byte`, or `8` if `byte` is zero. -/
def coldBitIndex (byte : UInt256) : Nat := coldBitScan byte 0 8

theorem coldScan_le (s : State) (expOff fuel : Nat) :
    ∀ i, coldScan s expOff i fuel ≤ i + fuel := by
  induction fuel with
  | zero => intro i; simp [coldScan]
  | succ fuel ih =>
      intro i
      by_cases hz : (loadedExponentByte s expOff i).toNat = 0
      · rw [coldScan, if_pos hz]
        have := ih (i + 1)
        omega
      · rw [coldScan, if_neg hz]
        omega

theorem coldScan_zeros (s : State) (expOff fuel : Nat) :
    ∀ i t, i ≤ t → t < coldScan s expOff i fuel →
      (loadedExponentByte s expOff t).toNat = 0 := by
  induction fuel with
  | zero => intro i t _ hhi; rw [coldScan] at hhi; omega
  | succ fuel ih =>
      intro i t hlo hhi
      by_cases hz : (loadedExponentByte s expOff i).toNat = 0
      · rw [coldScan, if_pos hz] at hhi
        rcases Nat.lt_or_ge t (i + 1) with h | h
        · have ht : t = i := by omega
          subst ht
          exact hz
        · exact ih (i + 1) t h hhi
      · rw [coldScan, if_neg hz] at hhi; omega

theorem coldScan_hit (s : State) (expOff fuel : Nat) :
    ∀ i, coldScan s expOff i fuel < i + fuel →
      ¬ (loadedExponentByte s expOff (coldScan s expOff i fuel)).toNat = 0 := by
  induction fuel with
  | zero => intro i hlt; rw [coldScan] at hlt; omega
  | succ fuel ih =>
      intro i hlt
      by_cases hz : (loadedExponentByte s expOff i).toNat = 0
      · rw [coldScan, if_pos hz] at hlt ⊢
        exact ih (i + 1) (by omega)
      · rw [coldScan, if_neg hz] at hlt ⊢
        exact hz

theorem coldByteIndex_le (s : State) (expOff e : Nat) :
    coldByteIndex s expOff e ≤ e := by
  have := coldScan_le s expOff e 0
  simpa [coldByteIndex] using this

theorem coldByteIndex_zeros (s : State) (expOff e t : Nat)
    (ht : t < coldByteIndex s expOff e) :
    (loadedExponentByte s expOff t).toNat = 0 :=
  coldScan_zeros s expOff e 0 t (Nat.zero_le t) ht

theorem coldByteIndex_hit (s : State) (expOff e : Nat)
    (hlt : coldByteIndex s expOff e < e) :
    ¬ (loadedExponentByte s expOff (coldByteIndex s expOff e)).toNat = 0 :=
  coldScan_hit s expOff e 0 (by simpa [coldByteIndex] using hlt)

theorem coldBitScan_le (byte : UInt256) (fuel : Nat) :
    ∀ j, coldBitScan byte j fuel ≤ j + fuel := by
  induction fuel with
  | zero => intro j; simp [coldBitScan]
  | succ fuel ih =>
      intro j
      by_cases hz : (exponentBit byte j).toNat = 0
      · rw [coldBitScan, if_pos hz]
        have := ih (j + 1)
        omega
      · rw [coldBitScan, if_neg hz]
        omega

theorem coldBitScan_zeros (byte : UInt256) (fuel : Nat) :
    ∀ j t, j ≤ t → t < coldBitScan byte j fuel →
      (exponentBit byte t).toNat = 0 := by
  induction fuel with
  | zero => intro j t _ hhi; rw [coldBitScan] at hhi; omega
  | succ fuel ih =>
      intro j t hlo hhi
      by_cases hz : (exponentBit byte j).toNat = 0
      · rw [coldBitScan, if_pos hz] at hhi
        rcases Nat.lt_or_ge t (j + 1) with h | h
        · have ht : t = j := by omega
          subst ht
          exact hz
        · exact ih (j + 1) t h hhi
      · rw [coldBitScan, if_neg hz] at hhi; omega

theorem coldBitIndex_le (byte : UInt256) : coldBitIndex byte ≤ 8 := by
  have := coldBitScan_le byte 8 0
  simpa [coldBitIndex] using this

theorem coldBitIndex_zeros (byte : UInt256) (t : Nat)
    (ht : t < coldBitIndex byte) : (exponentBit byte t).toNat = 0 :=
  coldBitScan_zeros byte 8 0 t (Nat.zero_le t) ht

/-- Bridge between the machine-level bit extraction and its `Nat` model. -/
theorem exponentBit_toNat_eq_bitNat (byte : UInt256) (j : Nat) (hj : j < 8) :
    (exponentBit byte j).toNat = WordCorrect.exponentBitNat byte j := by
  have h := congrArg UInt256.toNat (WordCorrect.exponentBit_eq byte j hj)
  have hbit := WordCorrect.exponentBitNat_zero_or_one byte j
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : WordCorrect.exponentBitNat byte j < 2 ^ 256)]
    at h
  exact h

theorem bitPrefix_eq_zero (byte : UInt256) (n : Nat)
    (hz : ∀ j, j < n → WordCorrect.exponentBitNat byte j = 0) :
    WordCorrect.bitPrefix byte n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [WordCorrect.bitPrefix, ih (fun j hj => hz j (by omega)),
        hz n (by omega)]

theorem loadedExponentByte_lt256 (s : State) (expOff i : Nat) :
    (loadedExponentByte s expOff i).toNat < 256 := by
  unfold loadedExponentByte UInt256.byteAt
  rw [show (0 : UInt256).toNat = 0 by decide]
  rw [if_neg (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  have hand :
      ((MachineState.readWord s.executionEnv.calldata (expOff + i)).toNat >>>
        (8 * (31 - 0))) &&& 255 ≤ 255 := Nat.and_le_right
  have hlt :
      ((MachineState.readWord s.executionEnv.calldata (expOff + i)).toNat >>>
        (8 * (31 - 0))) &&& 255 < 2 ^ 256 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

/-- A nonzero byte has a set bit, so the cold bit search terminates. -/
theorem coldBitIndex_lt (byte : UInt256) (hbyte : byte.toNat < 256)
    (hnz : ¬ byte.toNat = 0) : coldBitIndex byte < 8 := by
  rcases Nat.lt_or_ge (coldBitIndex byte) 8 with h | h
  · exact h
  · exfalso
    have h8 : coldBitIndex byte = 8 :=
      Nat.le_antisymm (coldBitIndex_le byte) h
    have hz : ∀ j, j < 8 → WordCorrect.exponentBitNat byte j = 0 := by
      intro j hj
      rw [← exponentBit_toNat_eq_bitNat byte j hj]
      exact coldBitIndex_zeros byte j (by omega)
    have hpre := bitPrefix_eq_zero byte 8 hz
    rw [WordCorrect.bitPrefix_eight byte hbyte] at hpre
    exact hnz hpre

def bitProgressFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (start : Nat) : Nat → State
  | 0 => s
  | t + 1 =>
      bitStepProgress
        (bitProgressFrom s accumulatorWord count b e m baseOff expOff i offset
          byte rest start t)
        accumulatorWord count b e m baseOff expOff i (start + t) offset byte rest

@[simp] theorem bitProgressFrom_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i start t : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (bitProgressFrom s accumulatorWord count b e m baseOff expOff i offset byte
      rest start t).executionEnv = s.executionEnv := by
  induction t with
  | zero => rfl
  | succ t ih => simp [bitProgressFrom, ih]

@[simp] theorem bitProgressFrom_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i start t : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (bitProgressFrom s accumulatorWord count b e m baseOff expOff i offset byte
      rest start t).halt = s.halt := by
  induction t with
  | zero => rfl
  | succ t ih => simp [bitProgressFrom, ih]

def bitLoopStateFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (start t : Nat) : State :=
  innerLoop
    (bitProgressFrom s accumulatorWord count b e m baseOff expOff i offset byte
      rest start t)
    accumulatorWord count b e m baseOff expOff i offset byte rest (start + t)


def byteProgressFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (start : Nat) : Nat → State
  | 0 => s
  | t + 1 =>
      let before := byteProgressFrom s accumulatorWord count b e m baseOff
        expOff rest start t
      exponentBitProgress before accumulatorWord count b e m baseOff expOff
        (start + t) (UInt256.ofNat (expOff + (start + t)))
        (loadedExponentByte before expOff (start + t)) rest 8

@[simp] theorem byteProgressFrom_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff start t : Nat)
    (rest : List UInt256) :
    (byteProgressFrom s accumulatorWord count b e m baseOff expOff rest start
      t).executionEnv = s.executionEnv := by
  induction t with
  | zero => rfl
  | succ t ih => simp [byteProgressFrom, ih]

@[simp] theorem byteProgressFrom_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff start t : Nat)
    (rest : List UInt256) :
    (byteProgressFrom s accumulatorWord count b e m baseOff expOff rest start
      t).halt = s.halt := by
  induction t with
  | zero => rfl
  | succ t ih => simp [byteProgressFrom, ih]

def outerStateFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (start t : Nat) : State :=
  outerLoop
    (byteProgressFrom s accumulatorWord count b e m baseOff expOff rest start t)
    accumulatorWord count b e m baseOff expOff rest (start + t)


theorem coldBitScan_hit (byte : UInt256) (fuel : Nat) :
    ∀ j, coldBitScan byte j fuel < j + fuel →
      ¬ (exponentBit byte (coldBitScan byte j fuel)).toNat = 0 := by
  induction fuel with
  | zero => intro j hlt; rw [coldBitScan] at hlt; omega
  | succ fuel ih =>
      intro j hlt
      by_cases hz : (exponentBit byte j).toNat = 0
      · rw [coldBitScan, if_pos hz] at hlt ⊢
        exact ih (j + 1) (by omega)
      · rw [coldBitScan, if_neg hz] at hlt ⊢
        exact hz

theorem coldBitIndex_hit (byte : UInt256) (h : coldBitIndex byte < 8) :
    ¬ (exponentBit byte (coldBitIndex byte)).toNat = 0 :=
  coldBitScan_hit byte 8 0 (by exact h)

/-- Accumulated state after running the hot bit loop from `start` to 8. -/
def bitFinalFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (start : Nat) : State :=
  bitProgressFrom s accumulatorWord count b e m baseOff expOff i offset byte
    rest start (8 - start)

/-- Accumulated state after running the hot byte loop from `start` to `e`. -/
def byteFinalFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (start : Nat) : State :=
  byteProgressFrom s accumulatorWord count b e m baseOff expOff rest start
    (e - start)


/-! ### The exponent phase: cold prefix followed by the hot loop -/

/-- The exponent byte the cold search stops on. -/
def coldPhaseByte (s : State) (expOff e : Nat) : UInt256 :=
  loadedExponentByte s expOff (coldByteIndex s expOff e)

/-- The bit index the cold search stops on. -/
def coldPhaseBit (s : State) (expOff e : Nat) : Nat :=
  coldBitIndex (coldPhaseByte s expOff e)

/-- Calldata offset of the exponent byte the cold search stops on. -/
def coldPhaseOffset (s : State) (expOff e : Nat) : UInt256 :=
  UInt256.ofNat (expOff + coldByteIndex s expOff e)

/-- S2b: the first set bit copies `base` into the accumulator instead of
running a square and a product. -/
def coldPhaseHit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  coldCopied s accumulatorWord count b e m baseOff expOff
    (coldByteIndex s expOff e) (coldPhaseOffset s expOff e)
    (coldPhaseByte s expOff e) rest (coldPhaseBit s expOff e)

/-- S2b resumes the hot inner loop one bit past the one that was found. -/
def coldPhaseStart (s : State) (expOff e : Nat) : Nat := coldPhaseBit s expOff e + 1

/-- Memory state after finishing the byte the cold search stopped on. -/
def coldPhaseBits (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  bitFinalFrom (coldPhaseHit s accumulatorWord count b e m baseOff expOff rest)
    accumulatorWord count b e m baseOff expOff (coldByteIndex s expOff e)
    (coldPhaseOffset s expOff e) (coldPhaseByte s expOff e) rest
    (coldPhaseStart s expOff e)

/-- Memory state after the remaining hot exponent bytes. -/
def coldPhaseTail (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  byteFinalFrom (coldPhaseBits s accumulatorWord count b e m baseOff expOff rest)
    accumulatorWord count b e m baseOff expOff rest (coldByteIndex s expOff e + 1)

/-- Memory state after the whole exponent phase.  For an all-zero exponent the
cold path writes nothing, so the state is unchanged. -/
def exponentPhaseState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  if coldByteIndex s expOff e = e then s
  else coldPhaseTail s accumulatorWord count b e m baseOff expOff rest

@[simp] theorem coldPhaseHit_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) :
    (coldPhaseHit s accumulatorWord count b e m baseOff expOff
      rest).executionEnv = s.executionEnv := by
  simp [coldPhaseHit, coldCopied, BigHelpers.copyReturned, coldCopyState, coldBitLoop]

@[simp] theorem coldPhaseHit_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) :
    (coldPhaseHit s accumulatorWord count b e m baseOff expOff rest).halt =
      s.halt := by
  simp [coldPhaseHit, coldCopied, BigHelpers.copyReturned, coldCopyState, coldBitLoop]

@[simp] theorem coldPhaseBits_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) :
    (coldPhaseBits s accumulatorWord count b e m baseOff expOff
      rest).executionEnv = s.executionEnv := by
  simp [coldPhaseBits, bitFinalFrom]

@[simp] theorem coldPhaseBits_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) :
    (coldPhaseBits s accumulatorWord count b e m baseOff expOff rest).halt =
      s.halt := by
  simp [coldPhaseBits, bitFinalFrom]

@[simp] theorem coldPhaseTail_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) :
    (coldPhaseTail s accumulatorWord count b e m baseOff expOff
      rest).executionEnv = s.executionEnv := by
  simp [coldPhaseTail, byteFinalFrom]

@[simp] theorem coldPhaseTail_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) :
    (coldPhaseTail s accumulatorWord count b e m baseOff expOff rest).halt =
      s.halt := by
  simp [coldPhaseTail, byteFinalFrom]

@[simp] theorem exponentPhaseState_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) :
    (exponentPhaseState s accumulatorWord count b e m baseOff expOff
      rest).executionEnv = s.executionEnv := by
  unfold exponentPhaseState
  split
  · rfl
  · simp

@[simp] theorem exponentPhaseState_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) :
    (exponentPhaseState s accumulatorWord count b e m baseOff expOff
      rest).halt = s.halt := by
  unfold exponentPhaseState
  split
  · rfl
  · simp


end ColdPath

end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
