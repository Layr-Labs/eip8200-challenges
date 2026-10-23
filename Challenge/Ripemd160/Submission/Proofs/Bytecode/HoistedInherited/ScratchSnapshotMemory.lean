import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.FusedTerminalMemory

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ScratchSnapshotMemory
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open HoistedInherited.Pair13PoolRaw

def prefixMemory (m : ByteArray) : ByteArray :=
  copyV2 (copyV2 (copyV2 m 162 144) 178 196) 252 234

/-- Full-width snapshot. Bytes 302..317 are dead until the writer overwrites them. -/
def copied32 (m : ByteArray) : ByteArray :=
  MachineState.writeBytes (prefixMemory m) (MachineState.readPadded (prefixMemory m) 268 32) 286

theorem snapshotWord (m : ByteArray) (src dst : Nat) :
    PairedScheduleMemory.writeWord m dst (MachineState.readWord m src) =
      MachineState.writeBytes m (MachineState.readPadded m src 32) dst := by
  unfold PairedScheduleMemory.writeWord
  congr 1
  apply ByteArray.ext
  apply Array.ext
  · simp [YulEvmCompiler.BytesLemmas.natToBytesPadded_size, Memory.readPadded_size]
  · intro i h1 h2
    have h1' : i < (Data.Bytes.natToBytesPadded (MachineState.readWord m src).toNat 32).size := h1
    have hi : i < 32 := by
      simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using h1'
    have h : (Data.Bytes.natToBytesPadded (MachineState.readWord m src).toNat 32)[i]?.getD 0 =
        (MachineState.readPadded m src 32)[i]?.getD 0 := by
      rw [PoolByte.encoded _ _ hi, PoolByte.read _ _ _ hi,
        Memory.readPadded_getElem?_getD, if_pos hi]
    rw [Memory.getD0_eq_getElem _ _ h1, Memory.getD0_eq_getElem _ _ h2] at h
    exact h

theorem copied_agree (m : ByteArray) (a : Nat) (ha : a < 302 ∨ 318 ≤ a) :
    (copied32 m)[a]?.getD 0 = (copiedV2 m)[a]?.getD 0 := by
  change (MachineState.writeBytes (prefixMemory m)
    (MachineState.readPadded (prefixMemory m) 268 32) 286)[a]?.getD 0 =
    (MachineState.writeBytes (prefixMemory m)
    (MachineState.readPadded (prefixMemory m) 268 16) 286)[a]?.getD 0
  simp only [MachineState.writeBytes_getElem?_getD, Memory.readPadded_size]
  by_cases h : 286 ≤ a ∧ a < 302
  · rw [if_pos (by omega), if_pos (by omega), Memory.readPadded_getElem?_getD,
      Memory.readPadded_getElem?_getD, if_pos (by omega), if_pos (by omega)]
  · rw [if_neg (by omega), if_neg (by omega)]

theorem pool_eq (m : ByteArray) : poolWordV2 (copied32 m) = poolWordV2 (copiedV2 m) := by
  funext i
  unfold poolWordV2 rawLoadV2
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro k hk
  apply copied_agree
  left
  have hb : poolAddrV2 i ≤ 270 := by
    unfold poolAddrV2
    split <;> omega
  omega

theorem chain_congr_at (m n : ByteArray) (ws : List (Nat × UInt256)) (a : Nat)
    (h : m[a]?.getD 0 = n[a]?.getD 0 ∨ ∃ x ∈ ws, x.1 ≤ a ∧ a < x.1 + 32) :
    (HoistedInherited.Pair13WriterRaw.writeChain m ws)[a]?.getD 0 =
      (HoistedInherited.Pair13WriterRaw.writeChain n ws)[a]?.getD 0 := by
  induction ws generalizing m n with
  | nil => rcases h with h | ⟨x,hx,_⟩; exact h; simp at hx
  | cons x xs ih =>
    rw [HoistedInherited.Pair13WriterRaw.writeChain_cons, HoistedInherited.Pair13WriterRaw.writeChain_cons]
    apply ih
    by_cases hx : x.1 ≤ a ∧ a < x.1 + 32
    · left
      rw [HoistedInherited.Shared32Scratch.writeWord_getD, HoistedInherited.Shared32Scratch.writeWord_getD,
        if_pos hx, if_pos hx]
    · rcases h with h | ⟨y,hy,ha⟩
      · left
        rw [HoistedInherited.Shared32Scratch.writeWord_getD, HoistedInherited.Shared32Scratch.writeWord_getD,
          if_neg hx, if_neg hx, h]
      · right
        have hy' : y ∈ xs := by
          rcases List.mem_cons.mp hy with hy | hy
          · subst y; exact False.elim (hx ha)
          · exact hy
        exact ⟨y,hy',ha⟩

theorem writer_getD_eq (m : ByteArray) (words : Nat → UInt256) (a : Nat) :
    (HoistedInherited.FusedTerminalMemory.writerMemory (copied32 m) words)[a]?.getD 0 =
      (HoistedInherited.FusedTerminalMemory.writerMemory (copiedV2 m) words)[a]?.getD 0 := by
  apply chain_congr_at
  by_cases h : a < 302 ∨ 318 ≤ a
  · exact Or.inl (copied_agree m a h)
  · right
    refine ⟨(288, HoistedInherited.FusedTerminalMemory.storedWord words (288,7)), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨(288,7), by decide, rfl⟩
    · constructor <;> omega

theorem chain_size (m : ByteArray) (ws : List (Nat × UInt256)) :
    (HoistedInherited.Pair13WriterRaw.writeChain m ws).size =
      ws.foldl (fun size x => max size (x.1 + 32)) m.size := by
  induction ws generalizing m with
  | nil => rfl
  | cons x xs ih =>
    rw [HoistedInherited.Pair13WriterRaw.writeChain_cons, ih, List.foldl_cons]
    congr 1
    simp only [PairedScheduleMemory.writeWord, MachineState.writeBytes_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size, if_neg (by decide : (32 : Nat) ≠ 0)]

theorem writer_size (m : ByteArray) (words : Nat → UInt256) :
    (HoistedInherited.FusedTerminalMemory.writerMemory m words).size = max m.size 1112 := by
  rw [HoistedInherited.FusedTerminalMemory.writerMemory, chain_size]
  simp only [HoistedInherited.PoolShape.writes, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil, Nat.max_assoc]
  norm_num

theorem byteArray_ext_getD (m n : ByteArray) (hs : m.size = n.size)
    (h : ∀ i : Nat, m[i]?.getD 0 = n[i]?.getD 0) : m = n := by
  apply ByteArray.ext
  apply Array.ext
  · exact hs
  · intro i h1 h2
    have hi := h i
    rw [Memory.getD0_eq_getElem _ _ h1, Memory.getD0_eq_getElem _ _ h2] at hi
    exact hi

theorem writer_eq (m : ByteArray) (words : Nat → UInt256) :
    HoistedInherited.FusedTerminalMemory.writerMemory (copied32 m) words =
      HoistedInherited.FusedTerminalMemory.writerMemory (copiedV2 m) words := by
  have hs : (HoistedInherited.FusedTerminalMemory.writerMemory (copied32 m) words).size =
      (HoistedInherited.FusedTerminalMemory.writerMemory (copiedV2 m) words).size := by
    rw [writer_size, writer_size]
    simp only [copied32, copiedV2, prefixMemory, copyV2, MachineState.writeBytes_size,
      Memory.readPadded_size, if_false, Nat.max_assoc]
    norm_num
  exact byteArray_ext_getD _ _ hs (writer_getD_eq m words)

#print axioms pool_eq
#print axioms writer_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ScratchSnapshotMemory
