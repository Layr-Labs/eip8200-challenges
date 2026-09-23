import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableMemory
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StaggerTableMemory
def slots : Array Nat := #[6, 4, 0, 0, 4, 12, 5, 11, 14, 14, 13, 13, 10, 7, 7, 15, 7, 10, 10, 2, 2, 4, 4, 6, 12, 12, 1, 5, 1, 0, 1, 8, 11, 11, 15, 10, 15, 14, 6, 5, 5, 8, 9, 1, 1, 9, 9, 3, 11, 3, 9, 8, 8, 3, 3, 15, 15, 6, 6, 13, 5]
def pairIndices : Array Nat := #[3, 43, 20, 49, 22, 60, 58, 16, 52, 45, 18, 48, 25, 59, 8, 55, 14, 4, 11, 28, 18, 38, 56, 53, 25, 2, 46, 27, 20, 37, 7, 31, 54, 17, 9, 1, 46, 34, 52, 26, 20, 13, 3, 23, 11, 32, 39, 5, 44, 50, 33, 35, 3, 41, 25, 21, 11, 47, 14, 36, 9, 6, 57, 19, 22, 29, 40, 42, 14, 24, 20, 12, 9, 30, 54, 51, 33]

/-- The layout covers every official RIPEMD round pair. -/
theorem layout_valid : ∀ i : Fin 77,
    let j := pairIndices[i.val]!
    1 ≤ j ∧ j < 61 ∧ slots[j]! = Crypto.Ripemd160.r[i.val]! ∧
      slots[j - 1]! = Crypto.Ripemd160.rP[i.val + 3]! := by decide

theorem slots_lt (i : Nat) (hi : i < 61) : slots[i]! < 16 := by
  have h : ∀ j : Fin 61, slots[j.val]! < 16 := by decide
  exact h ⟨i, hi⟩

def tableWords (words : Nat → UInt256) (j : Nat) : UInt256 := words slots[j]!
def resultMemory (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  storeDescending memory (tableWords words) 0 61

/-- The dual-lane value the S51 writer leaves in slot 0 once the mask at pc 873 is gone.
Written with `ofNat` rather than `UInt256.mul` on purpose: there is no multiplication
`toNat` lemma anywhere in this import closure, so the `mul` form would be unanalysable in
exactly the modules that must reason about it. -/
def dualLane (w : UInt256) : UInt256 := UInt256.ofNat (2 ^ 144 * w.toNat + w.toNat)

theorem dualLane_toNat (w : UInt256) (hw : w.toNat < 2 ^ 32) :
    (dualLane w).toNat = 2 ^ 144 * w.toNat + w.toNat := by
  rw [dualLane, Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hb : 2 ^ 144 * w.toNat ≤ 2 ^ 144 * (2 ^ 32 - 1) := Nat.mul_le_mul le_rfl (by omega)
  have hc : (2:Nat) ^ 144 * (2 ^ 32 - 1) + 2 ^ 32 < 2 ^ 256 := by norm_num
  omega

/-- The cand873 obligation is blind below byte 14.  Verified against the definitions:
`Ready.paired` reads at `18 * pairIndices[i]!` and `layout_valid` gives `1 ≤ pairIndices[i]!`
(lowest byte 18); `Ready.scalar 0` reads address 0 only through `low32`, i.e. bytes 28..31;
`Context.lowClear`'s `% 2 ^ 144` is bytes 14..31; `PairStoreGap.GapClear` is `18*j+k` with
`8 ≤ j` and `14 ≤ k` (lowest byte 158).  So a difference confined to bytes 0..13 is invisible
to the entire subsystem, and this single relation carries it. -/
def AgreeFrom14 (m m' : ByteArray) : Prop :=
  m.size = m'.size ∧ ∀ j, 14 ≤ j → m[j]?.getD 0 = m'[j]?.getD 0

theorem AgreeFrom14.rfl' (m : ByteArray) : AgreeFrom14 m m := ⟨rfl, fun _ _ => rfl⟩

/-- Writing the SAME value at the SAME address to both sides preserves the relation, at any
address: inside the window both take the written byte, outside both are unchanged. -/
theorem AgreeFrom14.writeWord {m m' : ByteArray} (h : AgreeFrom14 m m') (a : Nat)
    (v : UInt256) :
    AgreeFrom14 (PairedScheduleMemory.writeWord m a v)
      (PairedScheduleMemory.writeWord m' a v) := by
  refine ⟨by simp only [PairedScheduleMemory.writeWord_size, h.1], ?_⟩
  intro j hj
  simp only [PairedScheduleMemory.writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  by_cases hin : a ≤ j ∧ j < a + 32
  · rw [if_pos hin, if_pos hin]
  · rw [if_neg hin, if_neg hin]
    exact h.2 j hj

/-- Every read at address 14 or above is the same on both sides. -/
theorem AgreeFrom14.readWord {m m' : ByteArray} (h : AgreeFrom14 m m') (A : Nat)
    (hA : 14 ≤ A) : MachineState.readWord m A = MachineState.readWord m' A := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  exact bytesToNatPadded_congrOffset _ _ _ _ _ (fun i _ => h.2 (A + i) (by omega))

/-- Byte `k` of a 32-byte big-endian word, for `k ≥ 14`, depends only on the word's low
144 bits.  This is the whole reason the dual lane at bits 144..175 is invisible to every
consumer that reads at address 14 or above. -/
theorem byte_of_mod (v w : UInt256) (h : v.toNat % 2 ^ 144 = w.toNat % 2 ^ 144)
    (k : Nat) (h14 : 14 ≤ k) (hk : k < 32) :
    (Data.Bytes.natToBytesPadded v.toNat 32)[k]?.getD 0
      = (Data.Bytes.natToBytesPadded w.toNat 32)[k]?.getD 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hk,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hk]
  congr 1
  have hL : (256 : Nat) ^ (32 - 1 - k) = 2 ^ (8 * (32 - 1 - k)) := by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]
  have hsplit : (2 : Nat) ^ 144 = 2 ^ (8 * (32 - 1 - k)) * 2 ^ (144 - 8 * (32 - 1 - k)) := by
    rw [← Nat.pow_add]; congr 1; omega
  have key : ∀ x : Nat, x / 2 ^ (8 * (32 - 1 - k)) % 256
      = x % 2 ^ 144 / 2 ^ (8 * (32 - 1 - k)) % 256 := by
    intro x
    rw [hsplit, Nat.mod_mul_right_div_self, show (256 : Nat) = 2 ^ 8 by norm_num,
      Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : 8 ≤ 144 - 8 * (32 - 1 - k)))]
  rw [hL, key v.toNat, key w.toNat, h]

/-- Above byte 13 the dual lane is invisible: the extra copy sits at bits 144..175, i.e.
bytes 10..13, so every byte from 14 on agrees with the plain word. -/
theorem dualLane_byte (w : UInt256) (hw : w.toNat < 2 ^ 32) (k : Nat)
    (h14 : 14 ≤ k) (hk : k < 32) :
    (Data.Bytes.natToBytesPadded (dualLane w).toNat 32)[k]?.getD 0
      = (Data.Bytes.natToBytesPadded w.toNat 32)[k]?.getD 0 := by
  refine byte_of_mod (dualLane w) w ?_ k h14 hk
  rw [dualLane_toNat w hw, Nat.mul_add_mod]

/-- The table as the S51 writer leaves it once the mask at pc 873 is gone: slot 0, the
lowest, keeps the `2 ^ 144 + 1` dual lane instead of the plain word.  Slot 0 is written last
and nothing overwrites its top fourteen bytes, so bytes 10..13 of address 0 are the only
difference from `resultMemory`.  No round read covers them: `layout_valid` gives
`1 <= pairIndices[r]`, so every round window starts at address 18 or above, and the read at
address 0 is only ever taken through `low32`. -/
def resultMemory0 (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  PairedScheduleMemory.writeWord (resultMemory memory words) 0 (dualLane (words 6))

theorem slots_zero : slots[0]! = 6 := by decide

/-- Byte-level: the two table images differ only in bytes 10..13 of address 0. -/
theorem getD_resultMemory0 (memory : ByteArray) (words : Nat → UInt256)
    (hw : (words 6).toNat < 2 ^ 32) (j : Nat) (hj : 14 ≤ j) :
    (resultMemory0 memory words)[j]?.getD 0 = (resultMemory memory words)[j]?.getD 0 := by
  have hres : resultMemory memory words
      = PairedScheduleMemory.writeWord (storeDescending memory (tableWords words) 1 60) 0
        (words 6) := by
    change PairedScheduleMemory.writeWord (storeDescending memory (tableWords words) 1 60) 0
      (words slots[0]!) = _
    rw [slots_zero]
  rw [resultMemory0, hres]
  simp only [PairedScheduleMemory.writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  by_cases h32 : 0 ≤ j ∧ j < 0 + 32
  · rw [if_pos h32, if_pos h32, Nat.sub_zero]
    exact dualLane_byte (words 6) hw j hj (by omega)
  · rw [if_neg h32, if_neg h32]

theorem readWord_resultMemory0 (memory : ByteArray) (words : Nat → UInt256)
    (hw : (words 6).toNat < 2 ^ 32) (A : Nat) (hA : 14 ≤ A) :
    MachineState.readWord (resultMemory0 memory words) A
      = MachineState.readWord (resultMemory memory words) A := by
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  exact bytesToNatPadded_congrOffset _ _ _ _ _
    (fun i _ => getD_resultMemory0 memory words hw (A + i) (by omega))

theorem read_zero0 (memory : ByteArray) (words : Nat → UInt256) :
    MachineState.readWord (resultMemory0 memory words) 0 = dualLane (words 6) :=
  PairedScheduleMemory.read_writeWord _ _ _

/-- At address 0 the dual lane lives entirely above bit 31, so the low word is unchanged. -/
theorem read_zero0_low (memory : ByteArray) (words : Nat → UInt256)
    (hw : (words 6).toNat < 2 ^ 32) :
    (MachineState.readWord (resultMemory0 memory words) 0).toNat % 2 ^ 32
      = (MachineState.readWord (resultMemory memory words) 0).toNat % 2 ^ 32 := by
  have hres : MachineState.readWord (resultMemory memory words) 0 = words slots[0]! := by
    change MachineState.readWord (PairedScheduleMemory.writeWord
      (storeDescending memory (tableWords words) 1 60) 0 (words slots[0]!)) 0 = _
    exact PairedScheduleMemory.read_writeWord _ _ _
  rw [read_zero0, hres, slots_zero, dualLane_toNat _ hw,
    show (2:Nat) ^ 144 * (words 6).toNat = 2 ^ 32 * (2 ^ 112 * (words 6).toNat) from by
      rw [← Nat.mul_assoc, ← Nat.pow_add],
    Nat.mul_add_mod]

theorem read_round (memory : ByteArray) (words : Nat → UInt256)
    (r : Nat) (hr : r < 77) (hwords : ∀ i, i < 16 → (words i).toNat < 2 ^ 32) :
    (MachineState.readWord (resultMemory memory words) (18 * pairIndices[r]!)).toNat =
      (words Crypto.Ripemd160.r[r]!).toNat + (words Crypto.Ripemd160.rP[r + 3]!).toNat * 2 ^ 144 := by
  obtain ⟨hpos, hlt, hleft, hright⟩ := layout_valid ⟨r, hr⟩
  change 1 ≤ pairIndices[r]! at hpos
  change pairIndices[r]! < 61 at hlt
  have h := read_pair memory (tableWords words) 0 61 pairIndices[r]!
    (by omega) (by omega)
    (hwords _ (slots_lt _ hlt)) (hwords _ (slots_lt _ (by omega)))
  simpa only [resultMemory, tableWords, hleft, hright] using h

theorem resultMemory_size (memory : ByteArray) (words : Nat → UInt256) :
    (resultMemory memory words).size = max memory.size 1112 := by
  exact storeDescending_size _ _ _ _ (by decide)

theorem read_resultMemory_outside (memory : ByteArray) (words : Nat → UInt256)
    (address : Nat) (ha : 1112 ≤ address) :
    MachineState.readWord (resultMemory memory words) address = MachineState.readWord memory address :=
  read_table_outside _ _ _ ha


theorem read_slot_low (memory : ByteArray) (words : Nat → UInt256)
    (j : Nat) (hj : j < 61) (hwords : ∀ i, i < 16 → (words i).toNat < 2 ^ 32) :
    (MachineState.readWord (resultMemory memory words) (18 * j)).toNat % 2 ^ 32 =
      (words slots[j]!).toNat := by
  by_cases hz : j = 0
  · subst j
    change (MachineState.readWord
      (PairedScheduleMemory.writeWord (storeDescending memory (tableWords words) 1 60)
        0 (words slots[0]!)) 0).toNat % 2 ^ 32 = _
    rw [PairedScheduleMemory.read_writeWord, Nat.mod_eq_of_lt (hwords _ (slots_lt 0 (by decide)))]
  · have h := read_pair memory (tableWords words) 0 61 j (by omega) (by omega)
      (hwords _ (slots_lt _ hj)) (hwords _ (slots_lt _ (by omega)))
    have hm := congrArg (fun n : Nat => n % 2 ^ 32) h
    simpa only [resultMemory, tableWords, Nat.add_mod, Nat.mul_mod,
      show (2:Nat)^144 % 2^32 = 0 by norm_num, Nat.mul_zero, Nat.add_zero,
      Nat.zero_mod, Nat.mod_eq_of_lt (hwords _ (slots_lt _ hj))] using hm

/-- Words may carry dead bits above bit 32, as long as they stay below `2 ^ 112`: every
round read still returns the two words verbatim, one per 144-bit half. -/
theorem read_round_wide (memory : ByteArray) (words : Nat → UInt256)
    (r : Nat) (hr : r < 77) (hwords : ∀ i, i < 16 → (words i).toNat < 2 ^ 112) :
    (MachineState.readWord (resultMemory memory words) (18 * pairIndices[r]!)).toNat =
      (words Crypto.Ripemd160.r[r]!).toNat + (words Crypto.Ripemd160.rP[r + 3]!).toNat * 2 ^ 144 := by
  obtain ⟨hpos, hlt, hleft, hright⟩ := layout_valid ⟨r, hr⟩
  change 1 ≤ pairIndices[r]! at hpos
  change pairIndices[r]! < 61 at hlt
  have h := read_pair_wide memory (tableWords words) 0 61 pairIndices[r]!
    (by omega) (by omega)
    (by have := hwords _ (slots_lt _ hlt); unfold tableWords; omega)
    (hwords _ (slots_lt _ (by omega)))
  simpa only [resultMemory, tableWords, hleft, hright] using h

theorem read_slot_low_wide (memory : ByteArray) (words : Nat → UInt256)
    (j : Nat) (hj : j < 61) (hwords : ∀ i, i < 16 → (words i).toNat < 2 ^ 112) :
    (MachineState.readWord (resultMemory memory words) (18 * j)).toNat % 2 ^ 32 =
      (words slots[j]!).toNat % 2 ^ 32 := by
  by_cases hz : j = 0
  · subst j
    change (MachineState.readWord
      (PairedScheduleMemory.writeWord (storeDescending memory (tableWords words) 1 60)
        0 (words slots[0]!)) 0).toNat % 2 ^ 32 = _
    rw [PairedScheduleMemory.read_writeWord]
  · have h := read_pair_wide memory (tableWords words) 0 61 j (by omega) (by omega)
      (by have := hwords _ (slots_lt _ hj); unfold tableWords; omega)
      (hwords _ (slots_lt _ (by omega)))
    unfold resultMemory
    rw [h]
    simp only [tableWords]
    omega

/-- Slot 0 is written last, so the first memory word is exactly the word in slot 0. -/
theorem read_zero (memory : ByteArray) (words : Nat → UInt256) :
    MachineState.readWord (resultMemory memory words) 0 = words slots[0]! := by
  change MachineState.readWord
    (PairedScheduleMemory.writeWord (storeDescending memory (tableWords words) 1 60)
      0 (words slots[0]!)) 0 = _
  exact PairedScheduleMemory.read_writeWord _ _ _

theorem getD_resultMemory0_outside (memory : ByteArray) (words : Nat → UInt256)
    (address : Nat) (ha : 1112 ≤ address) :
    (resultMemory0 memory words)[address]?.getD 0 = memory[address]?.getD 0 := by
  rw [resultMemory0]
  simp only [PairedScheduleMemory.writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (by omega)]
  exact StaggerTableMemory.getD_table_outside memory _ address ha

theorem read_resultMemory0_outside (memory : ByteArray) (words : Nat → UInt256)
    (address : Nat) (ha : 1112 ≤ address) :
    MachineState.readWord (resultMemory0 memory words) address
      = MachineState.readWord memory address := by
  rw [resultMemory0,
    PairedScheduleMemory.read_writeWord_disjoint _ _ _ _ (Or.inr (by omega)),
    read_resultMemory_outside _ _ _ ha]

#print axioms read_round_wide
#print axioms read_slot_low_wide
#print axioms layout_valid
#print axioms read_round
#print axioms resultMemory_size
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
