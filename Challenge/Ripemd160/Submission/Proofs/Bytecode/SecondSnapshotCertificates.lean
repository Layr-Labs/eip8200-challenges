import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScratchSnapshotMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolPadInvariant
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Endian
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotCertificates
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PoolShape PoolShapeV2

/-- Widening178→196 also requires this relation on the incoming table image. -/
def Repeat4 (m : ByteArray) : Prop :=
  ∀ k, k < 4 → m[206+k]?.getD 0 = m[224+k]?.getD 0

theorem source_repeat : ∀ k : Fin 4,
    FusedTerminalCertificates.resultSource (206+k.val) =
      FusedTerminalCertificates.resultSource (224+k.val) := by decide

theorem result_repeat (m : ByteArray) (lo hi : UInt256) (hc : ClearV2 m) :
    Repeat4 (FusedTerminalMemory.resultMemory m lo hi) := by
  intro k hk
  rw [FusedTerminalMemory.result_shape m lo hi hc,
    FusedTerminalMemory.result_shape m lo hi hc, source_repeat ⟨k,hk⟩]

def secondPrefix (m : ByteArray) : ByteArray :=
  Pair13PoolRaw.copyV2
    (MachineState.writeBytes (Pair13PoolRaw.copyV2 m 162 144)
      (MachineState.readPadded (Pair13PoolRaw.copyV2 m 162 144) 178 32) 196) 252 234

def copiedTwo (m : ByteArray) : ByteArray :=
  MachineState.writeBytes (secondPrefix m) (MachineState.readPadded (secondPrefix m) 268 32) 286

theorem copy_getD (m : ByteArray) (src dst n a : Nat) :
    (MachineState.writeBytes m (MachineState.readPadded m src n) dst)[a]?.getD 0 =
      if dst ≤ a ∧ a < dst+n then m[src+(a-dst)]?.getD 0 else m[a]?.getD 0 := by
  rw [MachineState.writeBytes_getElem?_getD, Memory.readPadded_size]
  by_cases h : dst ≤ a ∧ a < dst+n
  · rw [if_pos h, if_pos h, Memory.readPadded_getElem?_getD, if_pos (by omega)]
  · rw [if_neg h, if_neg h]

theorem second_getD (m : ByteArray) (a : Nat) :
    (copiedTwo m)[a]?.getD 0 =
      if 286 ≤ a ∧ a < 318 then m[a-18]?.getD 0
      else if 234 ≤ a ∧ a < 250 then m[a+18]?.getD 0
      else if 196 ≤ a ∧ a < 228 then m[a-18]?.getD 0
      else if 144 ≤ a ∧ a < 160 then m[a+18]?.getD 0 else m[a]?.getD 0 := by
  simp only [copiedTwo, secondPrefix, Pair13PoolRaw.copyV2, copy_getD]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega)

theorem first_getD (m : ByteArray) (a : Nat) :
    (ScratchSnapshotMemory.copied32 m)[a]?.getD 0 =
      if 286 ≤ a ∧ a < 318 then m[a-18]?.getD 0
      else if 234 ≤ a ∧ a < 250 then m[a+18]?.getD 0
      else if 196 ≤ a ∧ a < 212 then m[a-18]?.getD 0
      else if 144 ≤ a ∧ a < 160 then m[a+18]?.getD 0 else m[a]?.getD 0 := by
  simp only [ScratchSnapshotMemory.copied32, ScratchSnapshotMemory.prefixMemory,
    Pair13PoolRaw.copyV2, copy_getD]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega)

theorem second_agree (m : ByteArray) (a : Nat) (ha : a < 212 ∨ 228 ≤ a) :
    (copiedTwo m)[a]?.getD 0 = (ScratchSnapshotMemory.copied32 m)[a]?.getD 0 := by
  rw [second_getD, first_getD]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem second_pool_eq (m : ByteArray) (hr : Repeat4 m) :
    Pair13PoolRaw.poolWordV2 (copiedTwo m) =
      Pair13PoolRaw.poolWordV2 (ScratchSnapshotMemory.copied32 m) := by
  funext i
  unfold Pair13PoolRaw.poolWordV2 Pair13PoolRaw.rawLoadV2
  apply Word.word_ext
  rw [Bytes.readWord_toNat, Bytes.readWord_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro k hk
  by_cases ha : Pair13PoolRaw.poolAddrV2 i + k < 212 ∨
      228 ≤ Pair13PoolRaw.poolAddrV2 i + k
  · exact second_agree m _ ha
  · have hi : Pair13PoolRaw.poolAddrV2 i = 224 := by
      unfold Pair13PoolRaw.poolAddrV2 at *
      split at ha <;> omega
    rw [hi] at ha ⊢
    have hk4 : k < 4 := by omega
    rw [second_getD, first_getD,
      if_neg (by omega), if_neg (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show 224 + k - 18 = 206+k by omega]
    exact hr k hk4

theorem second_writer_eq (m : ByteArray) (words : Nat → UInt256) :
    FusedTerminalMemory.writerMemory (copiedTwo m) words =
      FusedTerminalMemory.writerMemory (ScratchSnapshotMemory.copied32 m) words := by
  have hs : (FusedTerminalMemory.writerMemory (copiedTwo m) words).size =
      (FusedTerminalMemory.writerMemory (ScratchSnapshotMemory.copied32 m) words).size := by
    rw [ScratchSnapshotMemory.writer_size, ScratchSnapshotMemory.writer_size]
    simp only [copiedTwo, secondPrefix, ScratchSnapshotMemory.copied32,
      ScratchSnapshotMemory.prefixMemory, Pair13PoolRaw.copyV2,
      MachineState.writeBytes_size, Memory.readPadded_size]
    norm_num
  apply ScratchSnapshotMemory.byteArray_ext_getD _ _ hs
  intro a
  apply ScratchSnapshotMemory.chain_congr_at
  by_cases ha : a < 212 ∨ 228 ≤ a
  · exact Or.inl (second_agree m a ha)
  · right
    refine ⟨(198,FusedTerminalMemory.storedWord words (198,13)), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨(198,13), by decide, rfl⟩
    · constructor <;> omega

theorem pad_skip1 : ∀ k : Fin 4, ∀ j : Fin 61, StaggerTablePad.keepPad j.val = false ∨
    206+k.val < 18*j.val ∨ 18*j.val+32 ≤ 206+k.val := by decide

theorem pad_skip2 : ∀ k : Fin 4, ∀ j : Fin 61, StaggerTablePad.keepPad j.val = false ∨
    224+k.val < 18*j.val ∨ 18*j.val+32 ≤ 224+k.val := by decide

theorem pad_repeat (m : ByteArray) (n : UInt256) :
    Repeat4 (StaggerTablePad.padRealResult m n) := by
  intro k hk
  rw [StaggerTablePad.padRealResult, StaggerTablePad.resultMemoryOver,
    StaggerTablePad.getD_storeSelected_skip _ _ _ 0 61 (206+k)
      (fun j _ hj => pad_skip1 ⟨k,hk⟩ ⟨j,hj⟩),
    StaggerTablePad.getD_storeSelected_skip _ _ _ 0 61 (224+k)
      (fun j _ hj => pad_skip2 ⟨k,hk⟩ ⟨j,hj⟩),
    StaggerTableSparse.zeroMemory_getD, StaggerTableSparse.zeroMemory_getD,
    if_pos (by omega), if_pos (by omega)]

theorem scratch_repeat (m : ByteArray) (lo hi : UInt256) (hr : Repeat4 m) :
    Repeat4 (Pair13Endian.scratchV2 m lo hi) := by
  intro k hk
  simp only [Pair13Endian.scratchV2, Shared32Scratch.writeWord_getD,
    if_neg (by omega : ¬ (252 ≤ 206+k ∧ 206+k < 252+32)),
    if_neg (by omega : ¬ (162 ≤ 206+k ∧ 206+k < 162+32)),
    if_neg (by omega : ¬ (252 ≤ 224+k ∧ 224+k < 252+32)),
    if_neg (by omega : ¬ (162 ≤ 224+k ∧ 224+k < 162+32))]
  exact hr k hk

#print axioms scratch_repeat
#print axioms result_repeat
#print axioms second_pool_eq
#print axioms second_writer_eq
#print axioms pad_repeat
end Challenge.Ripemd160.Submission.Proofs.Bytecode.SecondSnapshotCertificates
