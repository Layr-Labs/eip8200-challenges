import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolInvariant
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolPadInvariant
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StaggerTableSparse

/-! ### The pad-only table against its model, from byte 28

The machine builds the pad table over `zeroSuffix m`, which keeps bytes [0,28) of the incoming
memory; the model builds it over `zeroMemory m`.  Every selected store writes the same value to
both, so they agree from byte 28 -- with no hypothesis on the incoming first word. -/

theorem storeSelected_from28 {b b' : ByteArray}
    (h : ∀ j, 28 ≤ j → b[j]?.getD 0 = b'[j]?.getD 0)
    (words : Nat → UInt256) (keep : Nat → Bool) (first count : Nat) :
    ∀ j, 28 ≤ j → (storeSelected b words keep first count)[j]?.getD 0 =
      (storeSelected b' words keep first count)[j]?.getD 0 := by
  induction count generalizing first with
  | zero => exact h
  | succ count ih =>
    intro j hj
    rw [storeSelected, storeSelected]
    by_cases hk : keep first = true
    · simp only [if_pos hk, Shared32Scratch.writeWord_getD]
      split
      · rfl
      · exact ih (first + 1) j hj
    · simp only [if_neg hk]
      exact ih (first + 1) j hj

theorem padRealResult_from28 (m : ByteArray) (n : UInt256) :
    ∀ j, 28 ≤ j → (StaggerTablePad.padRealResult m n)[j]?.getD 0 =
      (StaggerTablePad.resultMemory m n)[j]?.getD 0 := by
  unfold StaggerTablePad.padRealResult StaggerTablePad.resultMemoryOver StaggerTablePad.resultMemory
  refine storeSelected_from28 (fun j hj => ?_) _ _ 0 61
  rw [zeroSuffix_getD, zeroMemory_getD]
  by_cases hj' : j < 1112
  · rw [if_pos ⟨hj, hj'⟩, if_pos hj']
  · rw [if_neg (by omega), if_neg hj']

/-- Byte 32 (slot 1's slack byte 14) is zero in the real pad table: neither slot 0 nor slot 1
is selected, and `zeroSuffix` clears it. -/
theorem padRealResult_byte32 (m : ByteArray) (n : UInt256) :
    (StaggerTablePad.padRealResult m n)[32]?.getD 0 = 0 := by
  rw [StaggerTablePad.padRealResult, StaggerTablePad.resultMemoryOver,
    StaggerTablePad.getD_storeSelected_skip _ _ _ 0 61 32 (fun k _ hk => by
      by_cases hk0 : k = 0
      · subst hk0; exact Or.inl (by decide)
      by_cases hk1 : k = 1
      · subst hk1; exact Or.inl (by decide)
      exact Or.inr (Or.inl (by omega))),
    zeroSuffix_getD, if_pos (by decide)]

theorem pad_ready (m : ByteArray) (n : UInt256) (words : Nat → UInt32)
    (h : StaggerMessage.Ready (StaggerTablePad.resultMemory m n) words) :
    StaggerMessage.Ready (StaggerTablePad.padRealResult m n) words :=
  PoolInvariant.ready_of_from28 _ _ words (padRealResult_from28 m n) (padRealResult_byte32 m n) h

/-! ### The actual image's zero set survives the pad-only block -/

theorem storeSelected_band (b : ByteArray) (words : Nat → UInt256)
    (hw : ∀ j, (words j).toNat < 2 ^ 112) (keep : Nat → Bool) (first count a : Nat)
    (hk : 14 ≤ a % 18) (hz : b[a]?.getD 0 = 0) :
    (storeSelected b words keep first count)[a]?.getD 0 = 0 := by
  induction count generalizing first with
  | zero => exact hz
  | succ count ih =>
    rw [storeSelected]
    split
    · exact PairStoreGap.writeWord_band _ _ _ (by omega) (hw first) a hk (ih (first + 1))
    · exact ih (first + 1)

theorem padRealResult_clear (m : ByteArray) (n : UInt256) (hn : n.toNat < 2 ^ 64) :
    PoolShapeV2.ClearV2 (StaggerTablePad.padRealResult m n) := by
  intro a ha
  obtain ⟨h36, h1056, hk⟩ := PoolShapeV2.zeroAddressesV2_band a ha
  unfold StaggerTablePad.padRealResult StaggerTablePad.resultMemoryOver
  apply storeSelected_band _ _
    (fun j => StaggerTablePad.padWordsDirty_bound n hn _) _ 0 61 a hk
  rw [zeroSuffix_getD, if_pos (by omega)]

theorem padRealChain_clear (m : ByteArray) (n : UInt256) (hn : n.toNat < 2 ^ 64) :
    PoolShapeV2.ClearV2 (StaggerTablePad.padRealChain m n) := by
  intro a ha
  obtain ⟨h36, h1056, hk⟩ := PoolShapeV2.zeroAddressesV2_band a ha
  have hl := StaggerTablePad.lowDirty_bound n hn
  have h128 : (UInt256.ofNat 128).toNat < 2 ^ 112 := by decide
  unfold StaggerTablePad.padRealChain StaggerTablePad.lowChainOver
  refine PairStoreGap.writeWord_band _ _ _ (by decide) h128 a hk ?_
  refine PairStoreGap.writeWord_band _ _ _ (by decide) h128 a hk ?_
  refine PairStoreGap.writeWord_band _ _ _ (by decide) h128 a hk ?_
  refine PairStoreGap.writeWord_band _ _ _ (by decide) hl a hk ?_
  refine PairStoreGap.writeWord_band _ _ _ (by decide) hl a hk ?_
  refine PairStoreGap.writeWord_band _ _ _ (by decide) hl a hk ?_
  rw [zeroSuffix_getD, if_pos (by omega)]

#print axioms pad_ready
#print axioms padRealResult_clear
#print axioms padRealChain_clear
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolPadInvariant
