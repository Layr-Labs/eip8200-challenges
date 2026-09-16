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
def lowerPairSlots : List Nat := [57, 55, 53, 51, 45, 39, 32, 24, 21, 17, 13, 10, 8]

def GapClear (memory : ByteArray) : Prop :=
  ∀ j, j ∈ lowerPairSlots → ∀ k, 14 ≤ k → k < 18 →
    memory[18 * j + k]?.getD 0 = 0

/-- The six bytes the schedule fan does not write, and which the eight unmasked pool loads
therefore read out of the previous table image.  `Shared32Scratch.fanMemory` writes
`28..45`, `46..77`, `78..93`, `96..127` and `130..145`; the fourteen-byte junk window of every
unmasked word lies inside those ranges except for these six, which are the two bytes below each
of the three fan bases 28, 96 and 130.  Keeping them zero is what bounds the junk below the
carry threshold `2 ^ 112 - 4` that `normalize` needs. -/
def PoolClear (memory : ByteArray) : Prop :=
  Precompile.bytesToNatPadded memory 26 2 = 0 ∧
    Precompile.bytesToNatPadded memory 94 2 = 0 ∧
    Precompile.bytesToNatPadded memory 128 2 = 0

/-- `PoolClear` reads only six bytes, so any image agreeing on them inherits it. -/
theorem poolClear_congr (m m' : ByteArray)
    (h : ∀ a, (26 ≤ a ∧ a < 28) ∨ (94 ≤ a ∧ a < 96) ∨ (128 ≤ a ∧ a < 130) →
      m'[a]?.getD 0 = m[a]?.getD 0) (hp : PoolClear m) : PoolClear m' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [StaggerTableMemory.bytesToNatPadded_congrOffset m' m 26 26 2
      (fun i hi => h (26 + i) (by omega))]
    exact hp.1
  · rw [StaggerTableMemory.bytesToNatPadded_congrOffset m' m 94 94 2
      (fun i hi => h (94 + i) (by omega))]
    exact hp.2.1
  · rw [StaggerTableMemory.bytesToNatPadded_congrOffset m' m 128 128 2
      (fun i hi => h (128 + i) (by omega))]
    exact hp.2.2

/-- Any store whose thirty-two byte window misses all six bytes keeps the invariant. -/
theorem writeWord_preserves_poolClear (memory : ByteArray) (value : UInt256) (address : Nat)
    (ha : ∀ a, (26 ≤ a ∧ a < 28) ∨ (94 ≤ a ∧ a < 96) ∨ (128 ≤ a ∧ a < 130) →
      ¬ (address ≤ a ∧ a < address + 32))
    (hg : PoolClear memory) :
    PoolClear (writeWord memory address value) := by
  refine poolClear_congr memory _ (fun a hA => ?_) hg
  simp only [writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (ha a hA)]

theorem scratchMemory_poolClear (memory : ByteArray) (low high : UInt256)
    (hg : PoolClear memory) :
    PoolClear (StaggerScratch.scratchMemory memory low high) := by
  unfold StaggerScratch.scratchMemory
  refine writeWord_preserves_poolClear _ _ _ (by intro a h; omega) ?_
  exact writeWord_preserves_poolClear _ _ _ (by intro a h; omega) hg

theorem lowerPairSlots_bounds (j : Nat) (hj : j ∈ lowerPairSlots) :
    8 ≤ j ∧ j ≤ 57 := by
  simp only [lowerPairSlots, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

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

#print axioms resultMemory_gapClear
#print axioms scratchMemory_gapClear
#print axioms poolClear_congr
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairStoreGap
