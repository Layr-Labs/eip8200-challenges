import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScratch

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreGap
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory StaggerTableMemory StaggerTableLayout

/-- The four bytes not overwritten when a clean adjacent pair is stored once.
The pair at address 36 is deliberately absent: it overlaps the endian scratch. -/
def lowerPairSlots : List Nat := [57, 55, 53, 51, 45, 43, 39, 32, 24, 21, 19, 17, 13, 10, 8]

def GapClear (memory : ByteArray) : Prop :=
  ∀ j, j ∈ lowerPairSlots → ∀ k, 14 ≤ k → k < 18 →
    memory[18 * j + k]?.getD 0 = 0

theorem lowerPairSlots_bounds (j : Nat) (hj : j ∈ lowerPairSlots) :
    8 ≤ j ∧ j ≤ 57 := by
  simp only [lowerPairSlots, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> decide

theorem encoded_prefix_zero (value : UInt256) (hv : value.toNat < 2 ^ 112)
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

/-- Every complete old table establishes the invariant, including the existing
dirty source-word representation. No assumption about the incoming gap bytes. -/
theorem resultMemory_gapClear (memory : ByteArray) (words : Nat → UInt256)
    (hw : ∀ i, i < 16 → (words i).toNat < 2 ^ 112) :
    GapClear (resultMemory memory words) := by
  intro j hj k hk0 hk1
  have hb := lowerPairSlots_bounds j hj
  change (storeDescending memory (tableWords words) 0 61)[18 * j + k]?.getD 0 = 0
  rw [getD_pair _ _ _ _ _ _ (by omega) (by omega) (by omega), if_neg (by omega)]
  exact encoded_prefix_zero _ (hw _ (slots_lt j (by omega))) k hk1

theorem writeWord_preserves_gapClear (memory : ByteArray) (value : UInt256)
    (address : Nat) (ha : address + 32 ≤ 158) (hg : GapClear memory) :
    GapClear (writeWord memory address value) := by
  intro j hj k hk0 hk1
  have hb := lowerPairSlots_bounds j hj
  simp only [writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (by omega)]
  exact hg j hj k hk0 hk1

theorem resultMemory0_gapClear (memory : ByteArray) (words : Nat → UInt256)
    (hw : ∀ i, i < 16 → (words i).toNat < 2 ^ 112) :
    GapClear (StaggerTableLayout.resultMemory0 memory words) := by
  rw [StaggerTableLayout.resultMemory0]
  exact writeWord_preserves_gapClear _ _ _ (by decide) (resultMemory_gapClear memory words hw)

theorem scratchMemory_gapClear (memory : ByteArray) (low high : UInt256)
    (hg : GapClear memory) :
    GapClear (StaggerScratch.scratchMemory memory low high) := by
  unfold StaggerScratch.scratchMemory
  apply writeWord_preserves_gapClear _ _ _ (by decide)
  exact writeWord_preserves_gapClear _ _ _ (by decide) hg

/-! ### Band bytes

A byte `a` with `14 ≤ a % 18` is covered by at most one 18-aligned 32-byte store, and there it
is one of the store's bytes 14..17 -- zero for any value below `2 ^ 112`. -/

theorem writeWord_band (memory : ByteArray) (address : Nat) (value : UInt256)
    (hs : address % 18 = 0) (hv : value.toNat < 2 ^ 112) (a : Nat) (hk : 14 ≤ a % 18)
    (hz : memory[a]?.getD 0 = 0) :
    (writeWord memory address value)[a]?.getD 0 = 0 := by
  simp only [writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  split
  · exact encoded_prefix_zero _ hv _ (by omega)
  · exact hz

theorem table_band (memory : ByteArray) (words : Nat → UInt256)
    (hw : ∀ i, i < 16 → (words i).toNat < 2 ^ 112) (a : Nat) (h18 : 18 ≤ a) (ha : a < 1098)
    (hk : 14 ≤ a % 18) :
    (resultMemory memory words)[a]?.getD 0 = 0 := by
  have he : a = 18 * (a / 18) + a % 18 := (Nat.div_add_mod a 18).symm
  change (storeDescending memory (tableWords words) 0 61)[a]?.getD 0 = 0
  rw [he, getD_pair _ _ _ _ _ _ (by omega) (by omega) (by omega), if_neg (by omega)]
  exact encoded_prefix_zero _ (hw _ (slots_lt _ (by omega))) _ (by omega)

#print axioms resultMemory_gapClear
#print axioms scratchMemory_gapClear
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreGap
