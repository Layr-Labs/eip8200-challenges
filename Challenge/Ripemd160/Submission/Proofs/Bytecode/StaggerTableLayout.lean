import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableMemory
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StaggerTableMemory
def slots : Array Nat := #[6, 6, 12, 1, 1, 5, 11, 11, 15, 14, 6, 4, 6, 13, 13, 10, 7, 10, 2, 2, 4, 4, 12, 12, 5, 5, 8, 11, 3, 11, 14, 14, 15, 15, 7, 7, 13, 5, 1, 8, 9, 8, 8, 3, 9, 9, 1, 0, 4, 0, 0, 1, 9, 3, 3, 15, 10, 10, 15, 6, 5]
def pairIndices : Array Nat := #[50, 46, 19, 28, 21, 37, 1, 34, 42, 52, 57, 29, 23, 13, 30, 55, 35, 48, 14, 38, 57, 10, 33, 43, 23, 49, 45, 5, 19, 9, 6, 39, 54, 17, 31, 11, 45, 8, 42, 3, 19, 16, 50, 12, 14, 27, 60, 22, 4, 44, 7, 56, 50, 26, 23, 20, 14, 53, 35, 58, 31, 24, 59, 18, 21, 47, 25, 40, 35, 2, 19, 15, 31, 51, 54, 41, 7]

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
    (MachineState.readWord (resultMemory memory words) (10 * pairIndices[r]!)).toNat % 2 ^ 112 =
      (words Crypto.Ripemd160.r[r]!).toNat + (words Crypto.Ripemd160.rP[r + 3]!).toNat * 2 ^ 80 := by
  obtain ⟨hpos, hlt, hleft, hright⟩ := layout_valid ⟨r, hr⟩
  change 1 ≤ pairIndices[r]! at hpos
  change pairIndices[r]! < 61 at hlt
  have h := read_pair memory (tableWords words) 0 61 pairIndices[r]!
    (by omega) (by omega)
    (hwords _ (slots_lt _ hlt)) (hwords _ (slots_lt _ (by omega)))
  simpa only [resultMemory, tableWords, hleft, hright] using h

theorem resultMemory_size (memory : ByteArray) (words : Nat → UInt256) :
    (resultMemory memory words).size = max memory.size 632 := by
  exact storeDescending_size _ _ _ _ (by decide)

theorem read_resultMemory_outside (memory : ByteArray) (words : Nat → UInt256)
    (address : Nat) (ha : 632 ≤ address) :
    MachineState.readWord (resultMemory memory words) address = MachineState.readWord memory address :=
  read_table_outside _ _ _ ha


theorem read_slot_low (memory : ByteArray) (words : Nat → UInt256)
    (j : Nat) (hj : j < 61) (hwords : ∀ i, i < 16 → (words i).toNat < 2 ^ 32) :
    (MachineState.readWord (resultMemory memory words) (10 * j)).toNat % 2 ^ 32 =
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
    rw [Nat.mod_mod_of_dvd _ (by norm_num : (2:Nat)^32 ∣ 2^112)] at hm
    simpa only [resultMemory, tableWords, Nat.add_mod, Nat.mul_mod,
      show (2:Nat)^80 % 2^32 = 0 by norm_num, Nat.mul_zero, Nat.add_zero,
      Nat.zero_mod, Nat.mod_eq_of_lt (hwords _ (slots_lt _ hj))] using hm

#print axioms layout_valid
#print axioms read_round
#print axioms resultMemory_size
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
