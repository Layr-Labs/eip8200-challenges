import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableSparse
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadOnlyMemory
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StaggerTableMemory StaggerTableLayout StaggerTableSparse

def keepPad (j : Nat) : Bool :=
  decide (slots[j]! = 0 ∨ slots[j]! = 14 ∨ slots[j]! = 15)

/-- The high bit-length word as the pad-only setup stores it: `n >>> 29` without the 32-bit
mask, so bits `n / 2 ^ 61` (fewer than three for realizable calldata) sit above the lane. -/
def highDirty (n : UInt256) : UInt256 := UInt256.shiftRight n (UInt256.ofNat 29)

/-- The low bit-length word as the pad-only setup stores it: `n <<< 3` without the 32-bit
mask, so `n / 2 ^ 29` (fewer than `2 ^ 35` for realizable calldata) dead lanes sit above it. -/
def lowDirty (n : UInt256) : UInt256 := UInt256.shiftLeft n (UInt256.ofNat 3)

/-- Pad-only table words: the exact words except for the unmasked slots 14 and 15. -/
def padWordsDirty (n : UInt256) (i : Nat) : UInt256 :=
  if i = 14 then lowDirty n else if i = 15 then highDirty n else PadOnlySchedule.padWords n i

def resultMemory (memory : ByteArray) (n : UInt256) : ByteArray :=
  storeSelected (zeroMemory memory) (tableWords (padWordsDirty n)) keepPad 0 61

/-- The pad table over an ARBITRARY base: `resultMemory`'s own definition with the base
generalised.  It carries NO `highZero` condition and is therefore valid at every calldata
size -- for `n < 2 ^ 29` it is the low block alone (`lowChainOver_eq_resultMemoryOver`), and
above it the low block followed by the high block (`highChain_eq_over`). -/
def resultMemoryOver (base : ByteArray) (n : UInt256) : ByteArray :=
  storeSelected base (tableWords (padWordsDirty n)) keepPad 0 61

/-- The pad table the machine really builds: the same selected stores over the base the
calldata copy actually leaves (`zeroSuffix`, which clears only from byte 28 up), not over the
model's fully cleared `zeroMemory`.  The two agree from byte 14 (`padRealResult_agree`). -/
def padRealResult (memory : ByteArray) (n : UInt256) : ByteArray :=
  resultMemoryOver (StaggerTableSparse.zeroSuffix memory) n

/-- Every selected store writes the SAME value at the SAME address on both sides, so the
whole table transports `AgreeFrom14` -- at any address, including the ones below 14. -/
theorem storeSelected_agree {b b' : ByteArray} (h : StaggerTableLayout.AgreeFrom14 b b')
    (words : Nat → UInt256) (keep : Nat → Bool) (first count : Nat) :
    StaggerTableLayout.AgreeFrom14 (storeSelected b words keep first count)
      (storeSelected b' words keep first count) := by
  induction count generalizing first with
  | zero => exact h
  | succ count ih =>
    rw [storeSelected, storeSelected]
    by_cases hk : keep first = true
    · rw [if_pos hk, if_pos hk]
      exact (ih (first + 1)).writeWord (18 * first) (words first)
    · rw [if_neg hk, if_neg hk]
      exact ih (first + 1)

theorem resultMemoryOver_agree {b b' : ByteArray} (h : StaggerTableLayout.AgreeFrom14 b b')
    (n : UInt256) :
    StaggerTableLayout.AgreeFrom14 (resultMemoryOver b n) (resultMemoryOver b' n) :=
  storeSelected_agree h _ _ 0 61

/-- Selected stores never touch an address that every selected window misses. -/
theorem getD_storeSelected_skip (memory : ByteArray) (words : Nat → UInt256)
    (keep : Nat → Bool) (first count address : Nat)
    (hout : ∀ k, first ≤ k → k < first + count →
      keep k = false ∨ address < 18 * k ∨ 18 * k + 32 ≤ address) :
    (StaggerTableSparse.storeSelected memory words keep first count)[address]?.getD 0 =
      memory[address]?.getD 0 := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    rw [StaggerTableSparse.storeSelected]
    have hrest := ih (first + 1) (fun k hk hk' => hout k (by omega) (by omega))
    split
    · rename_i hkeep
      simp only [PairedScheduleMemory.writeWord, MachineState.writeBytes_getElem?_getD,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      have h := hout first (by omega) (by omega)
      rw [if_neg (by simp only [hkeep, Bool.true_eq_false, false_or] at h; omega)]
      exact hrest
    · exact hrest

/-- The pad-only block leaves byte 0 exactly as it found it: slot 0 is never selected and
`zeroSuffix` clears only from byte 28 up. -/
theorem padRealResult_zero0 (memory : ByteArray) (n : UInt256) :
    (padRealResult memory n)[0]?.getD 0 = memory[0]?.getD 0 := by
  rw [padRealResult, resultMemoryOver,
    getD_storeSelected_skip _ _ _ 0 61 0 (fun k _ hk => by
      by_cases hk0 : k = 0
      · subst hk0; exact Or.inl (by decide)
      · exact Or.inr (Or.inl (by omega))),
    StaggerTableSparse.zeroSuffix_getD, if_neg (by omega)]

/-- Reality versus model for the whole pad table, at EVERY calldata size. -/
theorem padRealResult_agree (memory : ByteArray) (n : UInt256)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) :
    StaggerTableLayout.AgreeFrom14 (padRealResult memory n) (resultMemory memory n) :=
  resultMemoryOver_agree (StaggerTableSparse.zeroSuffix_agree memory hlow) n

/-- Reads at or above the table see the original memory, at every calldata size and with no
first-word hypothesis: the selected stores stop at 1112 and so does `zeroSuffix`. -/
theorem getD_padRealResult_outside (memory : ByteArray) (n : UInt256) (address : Nat)
    (ha : 1112 ≤ address) :
    (padRealResult memory n)[address]?.getD 0 = memory[address]?.getD 0 := by
  rw [padRealResult, resultMemoryOver,
    StaggerTableSparse.getD_storeSelected_outside _ _ _ _ _ _ (fun k _ hk => by omega),
    StaggerTableSparse.zeroSuffix_getD, if_neg (by omega)]

theorem read_padRealResult_outside (memory : ByteArray) (n : UInt256)
    (address : Nat) (ha : 1112 ≤ address) :
    MachineState.readWord (padRealResult memory n) address =
      MachineState.readWord memory address := by
  unfold MachineState.readWord
  congr 2
  apply Memory.readPadded_congr
  intro i hi
  exact getD_padRealResult_outside memory n (address + i) (by omega)

/-- The low 144 bits of the word at address 0 are bytes 14..31, so `AgreeFrom14` fixes them.
This is the only route to address 0: `AgreeFrom14.readWord` needs `14 ≤ A`. -/
theorem readWord_zero_mod (m : ByteArray) :
    (MachineState.readWord m 0).toNat % 2 ^ 144 = Precompile.bytesToNatPadded m 14 18 := by
  have hadd : Precompile.bytesToNatPadded m 0 32
      = Precompile.bytesToNatPadded m 0 14 * 256 ^ 18 + Precompile.bytesToNatPadded m 14 18 := by
    simpa using Bytes.bytesToNatPadded_add m 0 14 18
  have hlt : Precompile.bytesToNatPadded m 14 18 < 256 ^ 18 :=
    Bytes.bytesToNatPadded_lt_pow m 14 18
  have hpow : (256 : Nat) ^ 18 = 2 ^ 144 := by norm_num
  rw [Bytes.readWord_toNat, hadd, hpow, Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by rw [← hpow]; exact hlt)

theorem read_zero_mod_of_agree {m m' : ByteArray} (h : StaggerTableLayout.AgreeFrom14 m m') :
    (MachineState.readWord m 0).toNat % 2 ^ 144
      = (MachineState.readWord m' 0).toNat % 2 ^ 144 := by
  rw [readWord_zero_mod, readWord_zero_mod]
  exact StaggerTableMemory.bytesToNatPadded_congrOffset m m' 14 14 18
    (fun i _ => h.2 (14 + i) (by omega))

/-- The same agreement at the width every `Ready` consumer of address 0 uses. -/
theorem read_zero_low32_of_agree {m m' : ByteArray} (h : StaggerTableLayout.AgreeFrom14 m m') :
    (MachineState.readWord m 0).toNat % 2 ^ 32
      = (MachineState.readWord m' 0).toNat % 2 ^ 32 := by
  have hd : (2 : Nat) ^ 32 ∣ 2 ^ 144 := pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mod_of_dvd _ hd, ← Nat.mod_mod_of_dvd (MachineState.readWord m' 0).toNat hd,
    read_zero_mod_of_agree h]

theorem padWordsDirty_fourteen (n : UInt256) : padWordsDirty n 14 = lowDirty n := by
  simp [padWordsDirty]

theorem padWordsDirty_fifteen (n : UInt256) : padWordsDirty n 15 = highDirty n := by
  simp [padWordsDirty]

theorem padWordsDirty_ne (n : UInt256) (i : Nat) (hi14 : i ≠ 14) (hi15 : i ≠ 15) :
    padWordsDirty n i = PadOnlySchedule.padWords n i := by
  simp [padWordsDirty, hi14, hi15]

theorem lowLength_eq_padWords (n : UInt256) :
    PadOnlySchedule.lowLength n = PadOnlySchedule.padWords n 14 := by
  simp [PadOnlySchedule.padWords]

theorem highLength_eq_padWords (n : UInt256) :
    PadOnlySchedule.highLength n = PadOnlySchedule.padWords n 15 := by
  simp [PadOnlySchedule.padWords]

theorem lowDirty_shift (n : UInt256) (hn : n.toNat < 2 ^ 64) :
    (UInt256.shiftLeft n (UInt256.ofNat 3)).toNat = n.toNat * 2 ^ 3 := by
  have h := Word.shiftLeft_ofNat (value := n.toNat) (shift := 3) n.val.isLt (by decide)
    (by simp only [Nat.reducePow] at *; omega)
  rw [← Word.word_eq_ofNat_toNat n] at h
  rw [h, Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by simp only [Nat.reducePow] at *; omega)]

theorem lowDirty_toNat (n : UInt256) (hn : n.toNat < 2 ^ 64) :
    (lowDirty n).toNat = (PadOnlySchedule.lowLength n).toNat + n.toNat / 2 ^ 29 * 2 ^ 32 := by
  have hs := lowDirty_shift n hn
  unfold PadOnlySchedule.lowLength lowDirty
  rw [Word.word_toNat_land, hs]
  have hm : (UInt256.ofNat 0xffffffff).toNat = 2 ^ 32 - 1 := by decide
  rw [hm, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.reducePow]
  omega

theorem lowDirty_junk_lt (n : UInt256) (hn : n.toNat < 2 ^ 64) : n.toNat / 2 ^ 29 < 2 ^ 35 := by
  simp only [Nat.reducePow] at *
  omega

theorem highDirty_toNat (n : UInt256) :
    (highDirty n).toNat = (PadOnlySchedule.highLength n).toNat + n.toNat / 2 ^ 61 * 2 ^ 32 := by
  unfold highDirty PadOnlySchedule.highLength
  rw [Word.word_toNat_land, Word.shiftRight_toNat _ (by decide), Nat.shiftRight_eq_div_pow]
  have hm : (UInt256.ofNat 0xffffffff).toNat = 2 ^ 32 - 1 := by decide
  rw [hm, Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.reducePow]
  omega

theorem highDirty_junk_lt (n : UInt256) (hn : n.toNat < 2 ^ 64) : n.toNat / 2 ^ 61 < 8 := by
  simp only [Nat.reducePow] at *
  omega

private theorem masked_bound (value : UInt256) :
    (UInt256.land (UInt256.ofNat 0xffffffff) value).toNat < 2 ^ 32 := by
  rw [Word.word_toNat_land]
  have hm : (UInt256.ofNat 0xffffffff).toNat = 0xffffffff := by decide
  rw [hm]
  exact Nat.lt_of_le_of_lt Nat.and_le_left (by decide)

theorem padWords_bound (n : UInt256) (i : Nat) :
    (PadOnlySchedule.padWords n i).toNat < 2 ^ 32 := by
  unfold PadOnlySchedule.padWords
  split
  · decide
  · split
    · exact masked_bound _
    · split
      · exact masked_bound _
      · decide

theorem padWordsDirty_bound (n : UInt256) (hn : n.toNat < 2 ^ 64) (i : Nat) :
    (padWordsDirty n i).toNat < 2 ^ 112 := by
  unfold padWordsDirty
  split
  · unfold lowDirty
    rw [lowDirty_shift n hn]
    simp only [Nat.reducePow] at *
    omega
  · split
    · unfold highDirty
      rw [Word.shiftRight_toNat _ (by decide)]
      exact Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hn) (by decide)
    · exact Nat.lt_trans (padWords_bound n i) (by decide)

theorem resultMemory_eq_table (memory : ByteArray) (n : UInt256) (hn : n.toNat < 2 ^ 64) :
    resultMemory memory n = StaggerTableLayout.resultMemory memory (padWordsDirty n) := by
  unfold resultMemory
  refine (selected_eq_full memory (tableWords (padWordsDirty n)) keepPad 0 61
    (by decide) ?_ ?_).trans (erase_zeroMemory _ _)
  · intro j hj hj'
    exact padWordsDirty_bound n hn slots[j]!
  · intro j hj hj' hk
    have h : ¬ (slots[j]! = 0 ∨ slots[j]! = 14 ∨ slots[j]! = 15) :=
      of_decide_eq_false hk
    simp only [tableWords, padWordsDirty, PadOnlySchedule.padWords,
      if_neg (show slots[j]! ≠ 0 by omega), if_neg (show slots[j]! ≠ 14 by omega),
      if_neg (show slots[j]! ≠ 15 by omega)]

/-- Reads above the table see the original memory, for any calldata size word. -/
theorem read_resultMemory_outside (memory : ByteArray) (n : UInt256)
    (address : Nat) (ha : 1112 ≤ address) :
    MachineState.readWord (resultMemory memory n) address = MachineState.readWord memory address := by
  unfold MachineState.readWord
  congr 2
  apply Memory.readPadded_congr
  intro i hi
  unfold resultMemory
  rw [getD_storeSelected_outside _ _ _ _ _ _ (fun k hk hk' => by omega),
    zeroMemory_getD, if_neg (by omega)]


/-! ## M3b: the pad-only block stores in program order

The low block stores the unmasked low bit-length word `n <<< 3` at 162, 666, 144 and `0x80` at
522, 54, 36;
when `n >>> 29 ≠ 0` the high block then stores `n >>> 29` at 1008, 990, 648, 612, 270.
Only adjacent slots (18 bytes apart) overlap, and every overlapping pair is still written
higher-address first, so the result is the descending table store. -/

theorem padWriteWord_comm (memory : ByteArray) (a b : Nat) (va vb : UInt256)
    (hab : a + 32 ≤ b ∨ b + 32 ≤ a) :
    PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord memory a va) b vb =
      PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord memory b vb) a va := by
  apply ByteArray.ext_getElem
  · simp only [PairedScheduleMemory.writeWord_size]
    omega
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj]
    simp only [PairedScheduleMemory.writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases ha : a ≤ i ∧ i < a + 32
    · have hb : ¬ (b ≤ i ∧ i < b + 32) := by omega
      simp only [if_pos ha, if_neg hb]
    · by_cases hb : b ≤ i ∧ i < b + 32
      · simp only [if_pos hb, if_neg ha]
      · simp only [if_neg ha, if_neg hb]

def keepLow (j : Nat) : Bool :=
  decide (slots[j]! = 0 ∨ slots[j]! = 14)

/-- Memory after the low block (program order). -/
def lowChain (memory : ByteArray) (n : UInt256) : ByteArray :=
  PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord
    (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord
      (zeroMemory memory) 162 (lowDirty n)) 666 (lowDirty n))
      144 (lowDirty n)) 522 (UInt256.ofNat 128)) 54 (UInt256.ofNat 128))
    36 (UInt256.ofNat 128)

/-- The low block's six stores over an ARBITRARY base.  `lowChain memory = lowChainOver
(zeroMemory memory)` definitionally; the machine's real base is
`MachineState.writeBytes memory PadZeroPrefix.zeroBytes 28`, which is only `AgreeFrom14`
with `zeroMemory memory` once a previous block leaves a dual lane in bytes 10..13. -/
def lowChainOver (base : ByteArray) (n : UInt256) : ByteArray :=
  PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord
    (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord
      base 162 (lowDirty n)) 666 (lowDirty n))
      144 (lowDirty n)) 522 (UInt256.ofNat 128)) 54 (UInt256.ofNat 128))
    36 (UInt256.ofNat 128)

theorem lowChain_eq_over (memory : ByteArray) (n : UInt256) :
    lowChain memory n = lowChainOver (zeroMemory memory) n := rfl

/-- The pad block's real table image. -/
def padRealChain (memory : ByteArray) (n : UInt256) : ByteArray :=
  lowChainOver (StaggerTableSparse.zeroSuffix memory) n


/-- All six low-block stores are at addresses ≥ 36, and in any case writing the same value to
both sides preserves the relation, so the pad block transports `AgreeFrom14` verbatim. -/
theorem lowChainOver_agree {b b' : ByteArray}
    (h : StaggerTableLayout.AgreeFrom14 b b') (n : UInt256) :
    StaggerTableLayout.AgreeFrom14 (lowChainOver b n) (lowChainOver b' n) :=
  ((((((h.writeWord 162 (lowDirty n)).writeWord 666 (lowDirty n)).writeWord 144
    (lowDirty n)).writeWord 522 (UInt256.ofNat 128)).writeWord 54
    (UInt256.ofNat 128)).writeWord 36 (UInt256.ofNat 128))

/-- The real pad table agrees with the model from byte 14 up. -/
theorem padRealChain_agree (memory : ByteArray) (n : UInt256)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) :
    StaggerTableLayout.AgreeFrom14 (padRealChain memory n) (lowChain memory n) := by
  rw [lowChain_eq_over]
  exact lowChainOver_agree (StaggerTableSparse.zeroSuffix_agree memory hlow) n

/-- The high block's five stores of the unmasked high word (program order). -/
def highStores (memory : ByteArray) (n : UInt256) : ByteArray :=
  PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord
    (PairedScheduleMemory.writeWord (PairedScheduleMemory.writeWord memory
      1008 (highDirty n)) 990 (highDirty n)) 648 (highDirty n)) 612 (highDirty n)) 270 (highDirty n)

/-- The five high-block stores likewise. -/
theorem highStores_agree {b b' : ByteArray}
    (h : StaggerTableLayout.AgreeFrom14 b b') (n : UInt256) :
    StaggerTableLayout.AgreeFrom14 (highStores b n) (highStores b' n) :=
  (((((h.writeWord 1008 (highDirty n)).writeWord 990 (highDirty n)).writeWord 648
    (highDirty n)).writeWord 612 (highDirty n)).writeWord 270 (highDirty n))


/-- The low block then the high block IS the pad table, over ANY base and at ANY calldata
size: only adjacent slots overlap and every overlapping pair is still written higher-address
first.  Nothing here depends on the base being cleared. -/
theorem highChain_eq_over (base : ByteArray) (n : UInt256) :
    highStores (lowChainOver base n) n = resultMemoryOver base n := by
  unfold highStores lowChainOver
  rw [padWriteWord_comm _ 162 666 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 522 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 36 1008 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 36 990 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 36 648 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 36 612 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 36 270 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 522 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 54 1008 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 54 990 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 54 648 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 54 612 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 54 270 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 1008 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 990 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 648 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 612 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 270 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 1008 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 990 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 648 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 612 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 270 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 522 1008 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 522 990 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 522 648 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 522 612 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 666 1008 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 666 990 _ _ (Or.inl (by decide))]
  simp [resultMemoryOver, storeSelected, keepPad, tableWords, slots, padWordsDirty,
    PadOnlySchedule.padWords]

theorem highChain_eq (memory : ByteArray) (n : UInt256) :
    highStores (lowChain memory n) n = resultMemory memory n :=
  highChain_eq_over (zeroMemory memory) n

theorem lowChain_selected (memory : ByteArray) (n : UInt256) :
    lowChain memory n = storeSelected (zeroMemory memory) (tableWords (padWordsDirty n)) keepLow 0 61 := by
  unfold lowChain
  rw [padWriteWord_comm _ 162 666 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 144 522 _ _ (Or.inl (by decide)),
    padWriteWord_comm _ 162 522 _ _ (Or.inl (by decide))]
  simp [storeSelected, keepLow, tableWords, slots, padWordsDirty, PadOnlySchedule.padWords]

theorem highDirty_zero_lt (n : UInt256) (hz : highDirty n = UInt256.ofNat 0) : n.toNat < 2 ^ 64 := by
  have h := congrArg UInt256.toNat hz
  unfold highDirty at h
  rw [Word.shiftRight_toNat _ (by decide), Nat.shiftRight_eq_div_pow] at h
  have h0 : (UInt256.ofNat 0).toNat = 0 := by decide
  rw [h0] at h
  simp only [Nat.reducePow] at h ⊢
  omega

theorem lowChain_eq (memory : ByteArray) (n : UInt256) (hz : highDirty n = UInt256.ofNat 0) :
    lowChain memory n = resultMemory memory n := by
  have hn := highDirty_zero_lt n hz
  rw [lowChain_selected]
  unfold resultMemory
  rw [selected_eq_full memory (tableWords (padWordsDirty n)) keepLow 0 61 (by decide)
      (fun j _ _ => padWordsDirty_bound n hn slots[j]!) ?_,
    selected_eq_full memory (tableWords (padWordsDirty n)) keepPad 0 61 (by decide)
      (fun j _ _ => padWordsDirty_bound n hn slots[j]!) ?_]
  · intro j hj hj' hk
    have h : ¬ (slots[j]! = 0 ∨ slots[j]! = 14 ∨ slots[j]! = 15) := by simpa [keepPad] using hk
    simp only [tableWords, padWordsDirty, PadOnlySchedule.padWords,
      if_neg (show slots[j]! ≠ 0 by omega), if_neg (show slots[j]! ≠ 14 by omega),
      if_neg (show slots[j]! ≠ 15 by omega)]
  · intro j hj hj' hk
    have h : ¬ (slots[j]! = 0 ∨ slots[j]! = 14) := by simpa [keepLow] using hk
    by_cases h15 : slots[j]! = 15
    · simp only [tableWords, padWordsDirty, if_neg (show slots[j]! ≠ 14 by omega), if_pos h15, hz]
    · simp only [tableWords, padWordsDirty, PadOnlySchedule.padWords,
        if_neg (show slots[j]! ≠ 0 by omega), if_neg (show slots[j]! ≠ 14 by omega),
        if_neg h15]

/-- A word below `2 ^ 112` leaves the first eighteen bytes of its 32-byte encoding zero. -/
theorem padWord_prefix_zero (value : UInt256) (hv : value.toNat < 2 ^ 112)
    (i : Nat) (hi : i < 18) :
    (Data.Bytes.natToBytesPadded value.toNat 32)[i]?.getD 0 = 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by omega)]
  have hp : (256 : Nat) ^ 14 ≤ 256 ^ (32 - 1 - i) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hv' : value.toNat < 256 ^ (32 - 1 - i) := by
    calc
      value.toNat < 2 ^ 112 := hv
      _ = 256 ^ 14 := by norm_num
      _ ≤ _ := hp
  rw [Nat.div_eq_of_lt hv']
  rfl

theorem lowDirty_bound (n : UInt256) (hn : n.toNat < 2 ^ 64) : (lowDirty n).toNat < 2 ^ 112 := by
  rw [lowDirty, lowDirty_shift n hn]
  simp only [Nat.reducePow] at *
  omega

/-- The five windows the high block would write are already zero after the low block, for any
base that is zero on `[28,1112)`.  Four of them are untouched base bytes; the window at 648
runs into the low store at 666, whose first fourteen bytes are zero because the stored word is
below `2 ^ 112`. -/
theorem lowChainOver_high_zero (base : ByteArray) (n : UInt256)
    (hv : (lowDirty n).toNat < 2 ^ 112)
    (hbase : ∀ a, 28 ≤ a → a < 1112 → base[a]?.getD 0 = 0)
    (a : Nat)
    (ha : (270 ≤ a ∧ a < 302) ∨ (612 ≤ a ∧ a < 644) ∨ (648 ≤ a ∧ a < 680) ∨
      (990 ≤ a ∧ a < 1022) ∨ (1008 ≤ a ∧ a < 1040)) :
    (lowChainOver base n)[a]?.getD 0 = 0 := by
  simp only [lowChainOver, PairedScheduleMemory.writeWord,
    MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (by omega : ¬ (36 ≤ a ∧ a < 36 + 32)),
    if_neg (by omega : ¬ (54 ≤ a ∧ a < 54 + 32)),
    if_neg (by omega : ¬ (522 ≤ a ∧ a < 522 + 32)),
    if_neg (by omega : ¬ (144 ≤ a ∧ a < 144 + 32))]
  by_cases h666 : 666 ≤ a ∧ a < 666 + 32
  · rw [if_pos h666]
    exact padWord_prefix_zero _ hv _ (by omega)
  · rw [if_neg h666, if_neg (by omega : ¬ (162 ≤ a ∧ a < 162 + 32))]
    exact hbase a (by omega) (by omega)

/-- When `n >>> 29 = 0` the high block stores zero into five windows that are already zero, so
it changes nothing.  `hz` is consumed here, never discharged by the call site. -/
theorem highStores_noop (base : ByteArray) (n : UInt256)
    (hz : highDirty n = UInt256.ofNat 0)
    (hbase : ∀ a, 28 ≤ a → a < 1112 → base[a]?.getD 0 = 0)
    (hsize : 1112 ≤ base.size) :
    highStores (lowChainOver base n) n = lowChainOver base n := by
  have hv : (lowDirty n).toNat < 2 ^ 112 := lowDirty_bound n (highDirty_zero_lt n hz)
  have hlsize : 1040 ≤ (lowChainOver base n).size := by
    simp only [lowChainOver, PairedScheduleMemory.writeWord_size]
    omega
  unfold highStores
  rw [hz,
    PairedScheduleMemory.writeWord_zero_noop _ 1008 (by omega)
      (fun i hi => lowChainOver_high_zero base n hv hbase (1008 + i) (by omega)),
    PairedScheduleMemory.writeWord_zero_noop _ 990 (by omega)
      (fun i hi => lowChainOver_high_zero base n hv hbase (990 + i) (by omega)),
    PairedScheduleMemory.writeWord_zero_noop _ 648 (by omega)
      (fun i hi => lowChainOver_high_zero base n hv hbase (648 + i) (by omega)),
    PairedScheduleMemory.writeWord_zero_noop _ 612 (by omega)
      (fun i hi => lowChainOver_high_zero base n hv hbase (612 + i) (by omega)),
    PairedScheduleMemory.writeWord_zero_noop _ 270 (by omega)
      (fun i hi => lowChainOver_high_zero base n hv hbase (270 + i) (by omega))]

/-- Below `2 ^ 29` the low block alone already IS the pad table, over any cleared-from-28
base.  This is `lowChain_eq` generalised; it keeps the same `hz` and adds no other route. -/
theorem lowChainOver_eq_resultMemoryOver (base : ByteArray) (n : UInt256)
    (hz : highDirty n = UInt256.ofNat 0)
    (hbase : ∀ a, 28 ≤ a → a < 1112 → base[a]?.getD 0 = 0)
    (hsize : 1112 ≤ base.size) :
    lowChainOver base n = resultMemoryOver base n := by
  rw [← highChain_eq_over base n, highStores_noop base n hz hbase hsize]

/-- What the pad-only block leaves when it takes the `highZero` branch is exactly the pad
table over the real base.  `hz : highDirty n = 0` is REQUIRED: above `2 ^ 29` the machine runs
the high block as well and the real image is `highStores (padRealChain ...)`, which is the
same `padRealResult` by `highChain_eq_over` -- but it is NOT the six low stores. -/
theorem padRealChain_eq (memory : ByteArray) (n : UInt256)
    (hz : highDirty n = UInt256.ofNat 0) :
    padRealChain memory n = padRealResult memory n :=
  lowChainOver_eq_resultMemoryOver (StaggerTableSparse.zeroSuffix memory) n hz
    (fun a h28 h1112 => by rw [StaggerTableSparse.zeroSuffix_getD, if_pos ⟨h28, h1112⟩])
    (by rw [StaggerTableSparse.zeroSuffix_size]; omega)

/-- Above `2 ^ 29` the pad block runs the high block too, and lands on the SAME table. -/
theorem padRealHigh_eq (memory : ByteArray) (n : UInt256) :
    highStores (padRealChain memory n) n = padRealResult memory n :=
  highChain_eq_over (StaggerTableSparse.zeroSuffix memory) n

theorem readPadded_end (input : ByteArray) :
    MachineState.readPadded input input.size 1112 = StaggerTableSparse.zeroBytes := by
  simp [MachineState.readPadded, StaggerTableSparse.zeroBytes]

#print axioms padWords_bound
#print axioms highDirty_toNat
#print axioms resultMemory_eq_table
#print axioms read_resultMemory_outside
#print axioms highChain_eq
#print axioms lowChain_eq
#print axioms highChain_eq_over
#print axioms highStores_noop
#print axioms lowChainOver_eq_resultMemoryOver
#print axioms padRealChain_eq
#print axioms padRealHigh_eq
#print axioms padRealResult_agree
#print axioms read_zero_mod_of_agree
#print axioms read_padRealResult_outside
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad
