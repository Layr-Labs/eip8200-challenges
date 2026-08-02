import Challenge.Sha256.Reference.Proofs.Bytecode.Main
import Challenge.Sha256.Reference.Proofs.Bytecode.PaddedBlockBridge
import Challenge.Sha256.Reference.Proofs.Bytecode.Word
import YulEvmCompiler.BytesLemmas

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# Functional correctness of the reference initialization

The reference program packs the 64 SHA-256 round constants into bytes
`32 .. 287` and stores the eight initial hash words in 32-byte slots beginning
at byte `288`.  This module exposes those facts independently of the later
compression execution proof.
-/

namespace Challenge.Sha256.Reference.Proofs.Bytecode.InitializationCorrect

open EvmSemantics
open EvmSemantics.Crypto
open EvmSemantics.EVM

/-- The 32-bit round constant returned by the reference program's packed
constant-table addressing expression. -/
def kWord (memory : ByteArray) (j : Nat) : UInt256 :=
  let offset := (UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) +
    UInt256.ofNat 32).toNat
  UInt256.shiftRight (MachineState.readWord memory offset) (UInt256.ofNat 224)

private def kOffset (j : Nat) : Nat :=
  (UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 2) +
    UInt256.ofNat 32).toNat

private theorem kOffset_eq (j : Nat) (hj : j < 64) :
    kOffset j = 32 + 4 * j := by
  unfold kOffset
  rw [Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
  rw [Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A hash-state word at the reference program's 32-byte-strided layout. -/
def hWord (memory : ByteArray) (i : Nat) : UInt256 :=
  MachineState.readWord memory (288 + 32 * i)

/-- Reusable memory invariant consumed by the compression proof: the packed
round-constant reader and the strided hash-state reader agree with the pinned
SHA-256 specification arrays at every valid index. -/
def ConstantsCorrect (memory : ByteArray) : Prop :=
  (∀ j : Nat, j < 64 →
    kWord memory j = Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]!) ∧
  (∀ i : Nat, i < 8 →
    hWord memory i = Challenge.EvmProof.Word.ofUInt32 Sha256.H0[i]!)

/-- The fixed memory image produced by initialization. -/
def initializedMemory : ByteArray :=
  (Main.initializedState ByteArray.empty).memory

/-- The prefix after the eight packed-K stores and before the H0 stores. -/
private def kTableMemory : ByteArray :=
  (Artifact.initStores.take 8).foldl
    (fun memory w => MachineState.writeBytes memory
      (Data.Bytes.natToBytesPadded w.value.toNat 32) w.offset.toNat)
    ByteArray.empty

theorem initializedState_memory (input : ByteArray) :
    (Main.initializedState input).memory = initializedMemory := by
  rfl

@[simp] private theorem initBytes_size (n : Nat) :
    (Data.Bytes.natToBytesPadded n 32).size = 32 := by
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

@[simp] private theorem toNat32 : (32 : UInt256).toNat = 32 := by decide
@[simp] private theorem toNat64 : (64 : UInt256).toNat = 64 := by decide
@[simp] private theorem toNat96 : (96 : UInt256).toNat = 96 := by decide
@[simp] private theorem toNat128 : (128 : UInt256).toNat = 128 := by decide
@[simp] private theorem toNat160 : (160 : UInt256).toNat = 160 := by decide
@[simp] private theorem toNat192 : (192 : UInt256).toNat = 192 := by decide
@[simp] private theorem toNat224 : (224 : UInt256).toNat = 224 := by decide
@[simp] private theorem toNat256 : (256 : UInt256).toNat = 256 := by decide
@[simp] private theorem toNat288 : (288 : UInt256).toNat = 288 := by decide
@[simp] private theorem toNat320 : (320 : UInt256).toNat = 320 := by decide
@[simp] private theorem toNat352 : (352 : UInt256).toNat = 352 := by decide
@[simp] private theorem toNat384 : (384 : UInt256).toNat = 384 := by decide
@[simp] private theorem toNat416 : (416 : UInt256).toNat = 416 := by decide
@[simp] private theorem toNat448 : (448 : UInt256).toNat = 448 := by decide
@[simp] private theorem toNat480 : (480 : UInt256).toNat = 480 := by decide
@[simp] private theorem toNat512 : (512 : UInt256).toNat = 512 := by decide

@[simp] private theorem packed0_toNat :
    (0x428a2f9871374491b5c0fbcfe9b5dba53956c25b59f111f1923f82a4ab1c5ed5 :
      UInt256).toNat =
      0x428a2f9871374491b5c0fbcfe9b5dba53956c25b59f111f1923f82a4ab1c5ed5 := by decide
@[simp] private theorem packed1_toNat :
    (0xd807aa9812835b01243185be550c7dc372be5d7480deb1fe9bdc06a7c19bf174 :
      UInt256).toNat =
      0xd807aa9812835b01243185be550c7dc372be5d7480deb1fe9bdc06a7c19bf174 := by decide
@[simp] private theorem packed2_toNat :
    (0xe49b69c1efbe47860fc19dc6240ca1cc2de92c6f4a7484aa5cb0a9dc76f988da :
      UInt256).toNat =
      0xe49b69c1efbe47860fc19dc6240ca1cc2de92c6f4a7484aa5cb0a9dc76f988da := by decide
@[simp] private theorem packed3_toNat :
    (0x983e5152a831c66db00327c8bf597fc7c6e00bf3d5a7914706ca635114292967 :
      UInt256).toNat =
      0x983e5152a831c66db00327c8bf597fc7c6e00bf3d5a7914706ca635114292967 := by decide
@[simp] private theorem packed4_toNat :
    (0x27b70a852e1b21384d2c6dfc53380d13650a7354766a0abb81c2c92e92722c85 :
      UInt256).toNat =
      0x27b70a852e1b21384d2c6dfc53380d13650a7354766a0abb81c2c92e92722c85 := by decide
@[simp] private theorem packed5_toNat :
    (0xa2bfe8a1a81a664bc24b8b70c76c51a3d192e819d6990624f40e3585106aa070 :
      UInt256).toNat =
      0xa2bfe8a1a81a664bc24b8b70c76c51a3d192e819d6990624f40e3585106aa070 := by decide
@[simp] private theorem packed6_toNat :
    (0x19a4c1161e376c082748774c34b0bcb5391c0cb34ed8aa4a5b9cca4f682e6ff3 :
      UInt256).toNat =
      0x19a4c1161e376c082748774c34b0bcb5391c0cb34ed8aa4a5b9cca4f682e6ff3 := by decide
@[simp] private theorem packed7_toNat :
    (0x748f82ee78a5636f84c878148cc7020890befffaa4506cebbef9a3f7c67178f2 :
      UInt256).toNat =
      0x748f82ee78a5636f84c878148cc7020890befffaa4506cebbef9a3f7c67178f2 := by decide

private theorem shl8_eq_mul256 (w : UInt32) : w <<< 8 = w * 256 := by
  apply UInt32.ext
  simp [UInt32.toNat_shiftLeft, UInt32.toNat_mul, Nat.shiftLeft_eq]

private theorem mul256_or_byte (w : UInt32) (b : UInt8) :
    w * 256 ||| b.toUInt32 = w * 256 + b.toUInt32 := by
  apply UInt32.toBitVec_inj.1
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_add]
  symm
  apply BitVec.add_eq_or_of_and_eq_zero
  rw [← shl8_eq_mul256]
  simp only [UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32]
  ext i hi
  by_cases hi8 : i < 8
  · simp [hi8]
  · simp [hi8, BitVec.getLsbD_of_ge b.toBitVec i (by omega)]

private theorem readBE32_eq_bytes (bs : ByteArray) (off : Nat) :
    Sha256.readBE32 bs off = UInt32.ofNat
      (((((bs[off]?.getD 0).toNat * 256 +
          (bs[off + 1]?.getD 0).toNat) * 256 +
          (bs[off + 2]?.getD 0).toNat) * 256) +
        (bs[off + 3]?.getD 0).toNat) := by
  by_cases h0 : off < bs.size
  all_goals by_cases h1 : off + 1 < bs.size
  all_goals by_cases h2 : off + 2 < bs.size
  all_goals by_cases h3 : off + 3 < bs.size
  all_goals try omega
  all_goals
    simp [Sha256.readBE32, Std.Legacy.Range.forIn_eq_forIn_range', List.range',
      h0, h1, h2, h3, shl8_eq_mul256, mul256_or_byte]

private theorem readBE32_congr (a b : ByteArray) (aoff boff : Nat)
    (h : ∀ i, i < 4 →
      a[aoff + i]?.getD 0 = b[boff + i]?.getD 0) :
    Sha256.readBE32 a aoff = Sha256.readBE32 b boff := by
  rw [readBE32_eq_bytes, readBE32_eq_bytes]
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp only [Nat.add_zero] at h0
  rw [h0, h1, h2, h3]

private theorem readBE32_writeBytes_disjoint (bs bytes : ByteArray)
    (off writeStart : Nat)
    (hdisjoint : off + 4 ≤ writeStart ∨ writeStart + bytes.size ≤ off) :
    Sha256.readBE32 (MachineState.writeBytes bs bytes writeStart) off =
      Sha256.readBE32 bs off := by
  apply readBE32_congr
  intro i hi
  rw [MachineState.writeBytes_getElem?_getD, if_neg]
  rcases hdisjoint with hbefore | hafter
  · omega
  · omega

private theorem readBE32_writeBytes_inside (bs bytes : ByteArray)
    (off writeStart : Nat) (hstart : writeStart ≤ off)
    (hstop : off + 4 ≤ writeStart + bytes.size) :
    Sha256.readBE32 (MachineState.writeBytes bs bytes writeStart) off =
      Sha256.readBE32 bytes (off - writeStart) := by
  apply readBE32_congr
  intro i hi
  rw [MachineState.writeBytes_getElem?_getD, if_pos]
  · congr 2
    omega
  · constructor <;> omega

private theorem readBE32_natToBytesPadded_32 (n off : Nat)
    (hoff : off + 4 ≤ 32) :
    Sha256.readBE32 (Data.Bytes.natToBytesPadded n 32) off =
      UInt32.ofNat
        (((((UInt8.ofNat (n / 256 ^ (32 - 1 - off) % 256)).toNat * 256 +
          (UInt8.ofNat (n / 256 ^ (32 - 1 - (off + 1)) % 256)).toNat) * 256 +
          (UInt8.ofNat (n / 256 ^ (32 - 1 - (off + 2)) % 256)).toNat) * 256) +
          (UInt8.ofNat (n / 256 ^ (32 - 1 - (off + 3)) % 256)).toNat) := by
  rw [readBE32_eq_bytes]
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD n 32 off
      (by omega)]
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD n 32 (off + 1)
      (by omega)]
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD n 32 (off + 2)
      (by omega)]
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD n 32 (off + 3)
      (by omega)]

private theorem initializedMemory_kWord_eq_table (j : Nat) (hj : j < 64) :
    kWord initializedMemory j = kWord kTableMemory j := by
  unfold kWord
  change UInt256.shiftRight (MachineState.readWord initializedMemory (kOffset j))
      (UInt256.ofNat 224) =
    UInt256.shiftRight (MachineState.readWord kTableMemory (kOffset j))
      (UInt256.ofNat 224)
  rw [PaddedBlockBridge.shiftRight_readWord_224,
    PaddedBlockBridge.shiftRight_readWord_224]
  rw [kOffset_eq j hj]
  unfold initializedMemory kTableMemory Main.initializedState Main.initStart
  norm_num [Artifact.initStores, Main.applyInitStore, Challenge.Sha256.frame,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  repeat'
    rw [readBE32_writeBytes_disjoint _ _ _ _
      (by simp only [initBytes_size]; omega)]

private theorem initializedMemory_k_0_8 (j : Nat)
    (hlo : 0 ≤ j) (hhi : j < 8) :
    kWord initializedMemory j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]! := by
  rw [initializedMemory_kWord_eq_table j (by omega)]
  unfold kWord
  change UInt256.shiftRight (MachineState.readWord kTableMemory (kOffset j))
      (UInt256.ofNat 224) = _
  rw [kOffset_eq j (by omega), PaddedBlockBridge.shiftRight_readWord_224]
  unfold kTableMemory
  norm_num [Artifact.initStores]
  repeat'
    first
    | rw [readBE32_writeBytes_inside _ _ _ _
        (by omega) (by simp only [initBytes_size]; omega)]
    | rw [readBE32_writeBytes_disjoint _ _ _ _
        (by simp only [initBytes_size]; omega)]
  rw [readBE32_natToBytesPadded_32 _ _ (by omega)]
  interval_cases j <;>
    norm_num [Sha256.K, Challenge.EvmProof.Word.ofUInt32,
      Challenge.EvmProof.Word.word_toNat_ofNat] <;> decide

private theorem initializedMemory_k_8_16 (j : Nat)
    (hlo : 8 ≤ j) (hhi : j < 16) :
    kWord initializedMemory j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]! := by
  rw [initializedMemory_kWord_eq_table j (by omega)]
  unfold kWord
  change UInt256.shiftRight (MachineState.readWord kTableMemory (kOffset j))
      (UInt256.ofNat 224) = _
  rw [kOffset_eq j (by omega), PaddedBlockBridge.shiftRight_readWord_224]
  unfold kTableMemory
  norm_num [Artifact.initStores]
  repeat'
    first
    | rw [readBE32_writeBytes_inside _ _ _ _
        (by omega) (by simp only [initBytes_size]; omega)]
    | rw [readBE32_writeBytes_disjoint _ _ _ _
        (by simp only [initBytes_size]; omega)]
  rw [readBE32_natToBytesPadded_32 _ _ (by omega)]
  interval_cases j <;>
    norm_num [Sha256.K, Challenge.EvmProof.Word.ofUInt32,
      Challenge.EvmProof.Word.word_toNat_ofNat] <;> decide

private theorem initializedMemory_k_16_24 (j : Nat)
    (hlo : 16 ≤ j) (hhi : j < 24) :
    kWord initializedMemory j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]! := by
  rw [initializedMemory_kWord_eq_table j (by omega)]
  unfold kWord
  change UInt256.shiftRight (MachineState.readWord kTableMemory (kOffset j))
      (UInt256.ofNat 224) = _
  rw [kOffset_eq j (by omega), PaddedBlockBridge.shiftRight_readWord_224]
  unfold kTableMemory
  norm_num [Artifact.initStores]
  repeat'
    first
    | rw [readBE32_writeBytes_inside _ _ _ _
        (by omega) (by simp only [initBytes_size]; omega)]
    | rw [readBE32_writeBytes_disjoint _ _ _ _
        (by simp only [initBytes_size]; omega)]
  rw [readBE32_natToBytesPadded_32 _ _ (by omega)]
  interval_cases j <;>
    norm_num [Sha256.K, Challenge.EvmProof.Word.ofUInt32,
      Challenge.EvmProof.Word.word_toNat_ofNat] <;> decide

private theorem initializedMemory_k_24_32 (j : Nat)
    (hlo : 24 ≤ j) (hhi : j < 32) :
    kWord initializedMemory j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]! := by
  rw [initializedMemory_kWord_eq_table j (by omega)]
  unfold kWord
  change UInt256.shiftRight (MachineState.readWord kTableMemory (kOffset j))
      (UInt256.ofNat 224) = _
  rw [kOffset_eq j (by omega), PaddedBlockBridge.shiftRight_readWord_224]
  unfold kTableMemory
  norm_num [Artifact.initStores]
  repeat'
    first
    | rw [readBE32_writeBytes_inside _ _ _ _
        (by omega) (by simp only [initBytes_size]; omega)]
    | rw [readBE32_writeBytes_disjoint _ _ _ _
        (by simp only [initBytes_size]; omega)]
  rw [readBE32_natToBytesPadded_32 _ _ (by omega)]
  interval_cases j <;>
    norm_num [Sha256.K, Challenge.EvmProof.Word.ofUInt32,
      Challenge.EvmProof.Word.word_toNat_ofNat] <;> decide

private theorem initializedMemory_k_32_40 (j : Nat)
    (hlo : 32 ≤ j) (hhi : j < 40) :
    kWord initializedMemory j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]! := by
  rw [initializedMemory_kWord_eq_table j (by omega)]
  unfold kWord
  change UInt256.shiftRight (MachineState.readWord kTableMemory (kOffset j))
      (UInt256.ofNat 224) = _
  rw [kOffset_eq j (by omega), PaddedBlockBridge.shiftRight_readWord_224]
  unfold kTableMemory
  norm_num [Artifact.initStores]
  repeat'
    first
    | rw [readBE32_writeBytes_inside _ _ _ _
        (by omega) (by simp only [initBytes_size]; omega)]
    | rw [readBE32_writeBytes_disjoint _ _ _ _
        (by simp only [initBytes_size]; omega)]
  rw [readBE32_natToBytesPadded_32 _ _ (by omega)]
  interval_cases j <;>
    norm_num [Sha256.K, Challenge.EvmProof.Word.ofUInt32,
      Challenge.EvmProof.Word.word_toNat_ofNat] <;> decide

private theorem initializedMemory_k_40_48 (j : Nat)
    (hlo : 40 ≤ j) (hhi : j < 48) :
    kWord initializedMemory j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]! := by
  rw [initializedMemory_kWord_eq_table j (by omega)]
  unfold kWord
  change UInt256.shiftRight (MachineState.readWord kTableMemory (kOffset j))
      (UInt256.ofNat 224) = _
  rw [kOffset_eq j (by omega), PaddedBlockBridge.shiftRight_readWord_224]
  unfold kTableMemory
  norm_num [Artifact.initStores]
  repeat'
    first
    | rw [readBE32_writeBytes_inside _ _ _ _
        (by omega) (by simp only [initBytes_size]; omega)]
    | rw [readBE32_writeBytes_disjoint _ _ _ _
        (by simp only [initBytes_size]; omega)]
  rw [readBE32_natToBytesPadded_32 _ _ (by omega)]
  interval_cases j <;>
    norm_num [Sha256.K, Challenge.EvmProof.Word.ofUInt32,
      Challenge.EvmProof.Word.word_toNat_ofNat] <;> decide

private theorem initializedMemory_k_48_56 (j : Nat)
    (hlo : 48 ≤ j) (hhi : j < 56) :
    kWord initializedMemory j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]! := by
  rw [initializedMemory_kWord_eq_table j (by omega)]
  unfold kWord
  change UInt256.shiftRight (MachineState.readWord kTableMemory (kOffset j))
      (UInt256.ofNat 224) = _
  rw [kOffset_eq j (by omega), PaddedBlockBridge.shiftRight_readWord_224]
  unfold kTableMemory
  norm_num [Artifact.initStores]
  repeat'
    first
    | rw [readBE32_writeBytes_inside _ _ _ _
        (by omega) (by simp only [initBytes_size]; omega)]
    | rw [readBE32_writeBytes_disjoint _ _ _ _
        (by simp only [initBytes_size]; omega)]
  rw [readBE32_natToBytesPadded_32 _ _ (by omega)]
  interval_cases j <;>
    norm_num [Sha256.K, Challenge.EvmProof.Word.ofUInt32,
      Challenge.EvmProof.Word.word_toNat_ofNat] <;> decide

private theorem initializedMemory_k_56_64 (j : Nat)
    (hlo : 56 ≤ j) (hhi : j < 64) :
    kWord initializedMemory j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]! := by
  rw [initializedMemory_kWord_eq_table j (by omega)]
  unfold kWord
  change UInt256.shiftRight (MachineState.readWord kTableMemory (kOffset j))
      (UInt256.ofNat 224) = _
  rw [kOffset_eq j (by omega), PaddedBlockBridge.shiftRight_readWord_224]
  unfold kTableMemory
  norm_num [Artifact.initStores]
  rw [readBE32_writeBytes_inside _ _ _ _
    (by omega) (by simp only [initBytes_size]; omega)]
  rw [readBE32_natToBytesPadded_32 _ _ (by omega)]
  interval_cases j <;>
    norm_num [Sha256.K, Challenge.EvmProof.Word.ofUInt32,
      Challenge.EvmProof.Word.word_toNat_ofNat] <;> decide

private theorem initializedMemory_k (j : Nat) (hj : j < 64) :
    kWord initializedMemory j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]! := by
  by_cases h8 : j < 8
  · exact initializedMemory_k_0_8 j (by omega) h8
  by_cases h16 : j < 16
  · exact initializedMemory_k_8_16 j (by omega) h16
  by_cases h24 : j < 24
  · exact initializedMemory_k_16_24 j (by omega) h24
  by_cases h32 : j < 32
  · exact initializedMemory_k_24_32 j (by omega) h32
  by_cases h40 : j < 40
  · exact initializedMemory_k_32_40 j (by omega) h40
  by_cases h48 : j < 48
  · exact initializedMemory_k_40_48 j (by omega) h48
  by_cases h56 : j < 56
  · exact initializedMemory_k_48_56 j (by omega) h56
  · exact initializedMemory_k_56_64 j (by omega) hj

private theorem initializedMemory_h_fin (i : Fin 8) :
    hWord initializedMemory i.val =
      Challenge.EvmProof.Word.ofUInt32 Sha256.H0[i.val]! := by
  fin_cases i <;>
    norm_num [hWord, initializedMemory, Main.initializedState,
      Artifact.initStores, Main.applyInitStore, Main.initStart,
      Challenge.Sha256.frame]
  all_goals
    repeat'
      first
      | rw [Challenge.EvmProof.Memory.readWord_writeWord]
      | rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
          (by simp only [initBytes_size]; decide)]
    decide

theorem initializedState_kWord (input : ByteArray) (j : Nat) (hj : j < 64) :
    kWord (Main.initializedState input).memory j =
      Challenge.EvmProof.Word.ofUInt32 Sha256.K[j]! := by
  rw [initializedState_memory]
  exact initializedMemory_k j hj

theorem initializedState_hWord (input : ByteArray) (i : Nat) (hi : i < 8) :
    hWord (Main.initializedState input).memory i =
      Challenge.EvmProof.Word.ofUInt32 Sha256.H0[i]! := by
  rw [initializedState_memory]
  exact initializedMemory_h_fin ⟨i, hi⟩

theorem initializedState_constantsCorrect (input : ByteArray) :
    ConstantsCorrect (Main.initializedState input).memory := by
  constructor
  · exact fun j hj => initializedState_kWord input j hj
  · exact fun i hi => initializedState_hWord input i hi

end Challenge.Sha256.Reference.Proofs.Bytecode.InitializationCorrect
