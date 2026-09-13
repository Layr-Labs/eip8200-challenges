import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableMemory
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StaggerTableMemory
def slots : Array Nat := #[6, 6, 4, 4, 0, 0, 4, 12, 12, 5, 8, 11, 11, 14, 14, 13, 13, 10, 7, 15, 7, 7, 10, 10, 2, 2, 4, 6, 12, 1, 5, 1, 1, 0, 1, 8, 8, 3, 3, 9, 1, 9, 8, 9, 9, 3, 15, 10, 15, 6, 13, 5, 5, 11, 3, 11, 15, 15, 14, 6, 5]
def pairIndices : Array Nat := #[5, 40, 25, 54, 3, 51, 1, 20, 36, 41, 23, 55, 8, 50, 13, 46, 21, 6, 16, 31, 23, 59, 57, 37, 8, 4, 44, 30, 25, 58, 53, 35, 38, 22, 14, 2, 44, 56, 36, 29, 25, 18, 5, 27, 16, 11, 60, 7, 32, 39, 12, 47, 5, 10, 8, 26, 16, 45, 21, 48, 14, 9, 49, 24, 3, 33, 52, 43, 21, 28, 25, 17, 14, 34, 38, 42, 12]

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

#print axioms read_round_wide
#print axioms read_slot_low_wide
#print axioms layout_valid
#print axioms read_round
#print axioms resultMemory_size
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
