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

#print axioms layout_valid
#print axioms read_round
#print axioms resultMemory_size
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
