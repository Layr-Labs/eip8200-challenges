import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Memory
import EvmSemantics.Crypto.Ripemd160
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Layout
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairTable144Memory
def slots : Array Nat := #[14, 15, 3, 6, 9, 14, 1, 11, 8, 11, 13, 8, 1, 10, 13, 3, 13, 15, 10, 3, 4, 7, 10, 13, 6, 14, 12, 3, 14, 2, 5, 15, 11, 6, 7, 9, 4, 11, 4, 9, 15, 12, 4, 5, 10, 5, 13, 12, 15, 0, 3, 0, 11, 2, 8, 9, 1, 7, 5, 12, 0, 4, 2, 1, 14, 8, 2, 7, 2, 6, 8, 7, 1, 12, 5, 0, 10, 6]
def pairIndices : Array Nat := #[75, 6, 68, 50, 36, 30, 33, 21, 11, 4, 18, 9, 73, 14, 28, 48, 34, 38, 16, 72, 76, 24, 31, 19, 26, 49, 55, 74, 62, 5, 7, 54, 2, 44, 64, 20, 35, 1, 70, 56, 53, 71, 60, 69, 14, 52, 43, 47, 12, 4, 37, 13, 51, 8, 41, 61, 46, 27, 67, 17, 5, 58, 77, 29, 42, 49, 45, 39, 57, 59, 66, 22, 25, 63, 15, 65, 52, 3, 40, 10]

/-- The layout covers every official RIPEMD round pair. -/
theorem layout_valid : ∀ i : Fin 80,
    let j := pairIndices[i.val]!
    1 ≤ j ∧ j < 78 ∧ slots[j]! = Crypto.Ripemd160.r[i.val]! ∧
      slots[j - 1]! = Crypto.Ripemd160.rP[i.val]! := by decide

theorem slots_lt (i : Nat) (hi : i < 78) : slots[i]! < 16 := by
  have h : ∀ j : Fin 78, slots[j.val]! < 16 := by decide
  exact h ⟨i, hi⟩

def tableWords (words : Nat → UInt256) (j : Nat) : UInt256 := words slots[j]!
def resultMemory (memory : ByteArray) (words : Nat → UInt256) : ByteArray :=
  storeDescending memory (tableWords words) 0 78

theorem read_round (memory : ByteArray) (words : Nat → UInt256)
    (r : Nat) (hr : r < 80) (hwords : ∀ i, i < 16 → (words i).toNat < 2 ^ 32) :
    (MachineState.readWord (resultMemory memory words) (18 * pairIndices[r]!)).toNat =
      (words Crypto.Ripemd160.r[r]!).toNat + (words Crypto.Ripemd160.rP[r]!).toNat * 2 ^ 144 := by
  obtain ⟨hpos, hlt, hleft, hright⟩ := layout_valid ⟨r, hr⟩
  change 1 ≤ pairIndices[r]! at hpos
  change pairIndices[r]! < 78 at hlt
  have h := read_pair_toNat memory (tableWords words) 0 78 pairIndices[r]!
    (by omega) (by omega)
    (hwords _ (slots_lt _ hlt)) (hwords _ (slots_lt _ (by omega)))
  simpa only [resultMemory, tableWords, hleft, hright] using h

theorem resultMemory_size (memory : ByteArray) (words : Nat → UInt256) :
    (resultMemory memory words).size = max memory.size 1418 := by
  exact storeDescending_size _ _ _ _ (by decide)

theorem read_resultMemory_outside (memory : ByteArray) (words : Nat → UInt256)
    (address : Nat) (ha : 1418 ≤ address) :
    MachineState.readWord (resultMemory memory words) address = MachineState.readWord memory address :=
  read_table_outside _ _ _ ha

#print axioms layout_valid
#print axioms read_round
#print axioms resultMemory_size
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Layout
