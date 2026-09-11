import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelPadding
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

private theorem init_store_bound (s : State) (w : Artifact.InitStore)
    (hs : s.memory.size ≤ 192) (hw : w ∈ Artifact.initStores) :
    (Main.applyInitStore s w).memory.size ≤ 192 := by
  have hoff : w.offset.toNat + 32 ≤ 192 := by
    simp only [Artifact.initStores, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [Main.applyInitStore, MachineState.writeBytes_size]
  split
  · exact hs
  · have h32 : (Data.Bytes.natToBytesPadded w.value.toNat 32).size = 32 := by
      simp [Data.Bytes.natToBytesPadded, ByteArray.size]
    rw [h32]
    omega

private theorem initial_size (input : ByteArray) :
    (PaddingTrace.padLengthReady input).memory.size ≤ 192 := by
  have hfold : ∀ (ws : List Artifact.InitStore) (s : State),
      (∀ w, w ∈ ws → w ∈ Artifact.initStores) →
      s.memory.size ≤ 192 → (ws.foldl Main.applyInitStore s).memory.size ≤ 192 := by
    intro ws
    induction ws with
    | nil => intro s _ hs; simpa using hs
    | cons w ws ih =>
      intro s hmem hs
      simp only [List.foldl_cons]
      exact ih _ (fun x hx => hmem x (by simp [hx]))
        (init_store_bound s w hs (hmem w (by simp)))
  change (Main.initializedState input).memory.size ≤ 192
  apply hfold Artifact.initStores (Execution.mainStart input) (fun _ hw => hw)
  exact Nat.le_trans (Nat.le_of_eq (rfl : (Execution.mainStart input).memory.size = 0))
    (Nat.zero_le _)

private theorem paddedMemory_zero (input : ByteArray) (i : Nat) (hi : i < 32) :
    (Padding.paddedMemory (PaddingTrace.padLengthReady input).memory input)[704 + i]?.getD 0 = 0 := by
  have hp := Padding.input_and_footer_fit input.size
  unfold Padding.paddedMemory Padding.sentinelMemory Padding.copiedMemory
  rw [MachineState.writeBytes_getElem?_getD, Padding.lengthBytes_size,
    if_neg (by unfold Padding.messageOffset; omega)]
  rw [MachineState.writeBytes_getElem?_getD,
    if_neg (by unfold Padding.messageOffset; omega)]
  rw [MachineState.writeBytes_getElem?_getD,
    if_neg (by unfold Padding.messageOffset; omega)]
  exact Memory.getElem?_getD_eq_zero_of_size_le _ _ (by have h := initial_size input; omega)

theorem padReturned_zero (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < 32) :
    (PaddingTrace.padReturned input).memory[704 + i]?.getD 0 = 0 := by
  rw [PaddingTrace.padReturned_memory input hfit]
  exact paddedMemory_zero input i hi

private theorem paddedMemory_sentinel (input : ByteArray) :
    (Padding.paddedMemory (PaddingTrace.padLengthReady input).memory input)[736 + input.size]?.getD 0 = (128 : UInt8) := by
  have hp := Padding.input_and_footer_fit input.size
  unfold Padding.paddedMemory Padding.sentinelMemory
  rw [MachineState.writeBytes_getElem?_getD, Padding.lengthBytes_size,
    if_neg (by unfold Padding.messageOffset; omega)]
  rw [MachineState.writeBytes_getElem?_getD]
  simp [Padding.messageOffset]
  rfl

theorem padReturned_size (input : ByteArray) (hfit : CalldataFits input) :
    736 ≤ (PaddingTrace.padReturned input).memory.size := by
  have h := PaddingTrace.padReturned_memory input hfit (736 + input.size)
  rw [paddedMemory_sentinel] at h
  by_contra hn
  have hz := Memory.getElem?_getD_eq_zero_of_size_le
    (PaddingTrace.padReturned input).memory (736 + input.size) (by omega)
  rw [hz] at h
  contradiction

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelPadding
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelPadding.padReturned_zero
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelPadding.padReturned_size
