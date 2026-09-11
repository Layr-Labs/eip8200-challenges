import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-!
# The padding leaves the zero sentinel in place

The five IV stores write at 0x220..0x2bf and the padding writes at 0x2e0 and
above, so bytes 512..543 are never written: they are the zero fill of the
first IV store, and memory is at least 736 bytes long when padding returns.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelPadding

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

private theorem initStore_low (s : State) (w : Artifact.InitStore)
    (hw : w ∈ Artifact.initStores) (a : Nat) (ha : a < 544) :
    (Main.applyInitStore s w).memory[a]?.getD 0 = s.memory[a]?.getD 0 := by
  have hoff : 544 ≤ w.offset.toNat := by
    simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide
  simp only [Main.applyInitStore]
  rw [MachineState.writeBytes_getElem?_getD, if_neg (by omega)]

private theorem fold_low : ∀ (ws : List Artifact.InitStore) (s : State),
    (∀ w, w ∈ ws → w ∈ Artifact.initStores) → ∀ a, a < 544 →
    (ws.foldl Main.applyInitStore s).memory[a]?.getD 0 = s.memory[a]?.getD 0
  | [], _, _, _, _ => rfl
  | w :: ws, s, hmem, a, ha => by
    simp only [List.foldl_cons]
    rw [fold_low ws _ (fun x hx => hmem x (by simp [hx])) a ha]
    exact initStore_low s w (hmem w (by simp)) a ha

private theorem initialized_low (input : ByteArray) (a : Nat) (ha : a < 544) :
    (PaddingTrace.padLengthReady input).memory[a]?.getD 0 = 0 := by
  change (Main.initializedState input).memory[a]?.getD 0 = 0
  unfold Main.initializedState
  rw [fold_low Artifact.initStores (Execution.mainStart input) (fun _ hw => hw) a ha]
  exact Memory.getElem?_getD_eq_zero_of_size_le _ _
    (by have h0 : (Execution.mainStart input).memory.size = 0 := rfl; omega)

theorem padReturned_zero (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 32) :
    (PaddingTrace.padReturned input).memory[512 + i]?.getD 0 = 0 := by
  change (PaddingTrace.padFinalMemory input)[512 + i]?.getD 0 = 0
  rw [PaddingTrace.padFinalMemory_getD input hfit,
    if_neg (by unfold Padding.messageOffset; omega)]
  simp only [PaddingTrace.padSentinel, PaddingTrace.padCopied]
  rw [MachineState.writeBytes_getElem?_getD, if_neg (by unfold Padding.messageOffset; omega)]
  rw [MachineState.writeBytes_getElem?_getD, if_neg (by unfold Padding.messageOffset; omega)]
  exact initialized_low input (512 + i) (by omega)

theorem padReturned_size (input : ByteArray) (hfit : CalldataFits input) :
    544 ≤ (PaddingTrace.padReturned input).memory.size := by
  change 544 ≤ (PaddingTrace.padFinalMemory input).size
  rw [PaddingTrace.padFinalMemory_size input hfit]
  unfold Padding.messageOffset
  omega

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelPadding

#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelPadding.padReturned_zero
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelPadding.padReturned_size
