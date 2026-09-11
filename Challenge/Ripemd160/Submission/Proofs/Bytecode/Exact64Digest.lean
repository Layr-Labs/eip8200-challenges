import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputDigest

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

/-!
# The digest of the 64-byte patterned vector

Block 0 is the checked patterned block, already certified as `H1` by `PrefixStateData`.
Block 1 is the canonical padding block for a 64-byte message, a constant, so one kernel
compression finishes the hash.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Exact64Digest

open EvmSemantics.Crypto

/-- The 64-byte prefix of the patterned vector. -/
def input64 : ByteArray := ByteArray.mk #[
  0x07, 0x2c, 0x51, 0x76, 0x9b, 0xc0, 0xe5, 0x0a, 0x2f, 0x54,
  0x79, 0x9e, 0xc3, 0xe8, 0x0d, 0x32, 0x57, 0x7c, 0xa1, 0xc6,
  0xeb, 0x10, 0x35, 0x5a, 0x7f, 0xa4, 0xc9, 0xee, 0x13, 0x38,
  0x5d, 0x82, 0xa7, 0xcc, 0xf1, 0x16, 0x3b, 0x60, 0x85, 0xaa,
  0xcf, 0xf4, 0x19, 0x3e, 0x63, 0x88, 0xad, 0xd2, 0xf7, 0x1c,
  0x41, 0x66, 0x8b, 0xb0, 0xd5, 0xfa, 0x1f, 0x44, 0x69, 0x8e,
  0xb3, 0xd8, 0xfd, 0x22]

@[simp] theorem input64_size : input64.size = 64 := by decide

/-- The canonical padding block for a 64-byte message. -/
def finalBlock64 : ByteArray := ByteArray.mk #[
  0x80, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0x00, 0x02, 0, 0, 0, 0, 0, 0]

def finalWords64 : Array UInt32 :=
  #[0x00000080, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x00000200, 0]

/-- The chaining state after both blocks. -/
def state64 : Array UInt32 :=
  #[0xc8b0148a, 0x9bb38792, 0xaa732f1a, 0x95cea179, 0x17784eb0]

theorem canonicalTail_input64 :
    HashSpecBridge.canonicalTail input64 = finalBlock64 := by
  rw [HashSpecBridge.canonicalTail_eq]
  apply ByteArray.ext
  simp [input64, finalBlock64, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    ByteArray.data_append, ByteArray.size]

theorem read_final64 (i : Nat) (hi : i < 16) :
    Ripemd160.readLE32 finalBlock64 (i * 4) = finalWords64[i]! := by
  interval_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [finalBlock64, finalWords64, Ripemd160.readLE32,
        List.range', List.foldl, ByteArray.size,
        ByteArray.getElem_eq_getElem_data] <;>
    try (apply UInt32.eq_of_toBitVec_eq; decide)

theorem schedule_final64 : CompressionCorrect.schedule finalBlock64 0 = finalWords64 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 finalBlock64 (0 * 4) = finalWords64[0]! from read_final64 0 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (1 * 4) = finalWords64[1]! from read_final64 1 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (2 * 4) = finalWords64[2]! from read_final64 2 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (3 * 4) = finalWords64[3]! from read_final64 3 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (4 * 4) = finalWords64[4]! from read_final64 4 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (5 * 4) = finalWords64[5]! from read_final64 5 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (6 * 4) = finalWords64[6]! from read_final64 6 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (7 * 4) = finalWords64[7]! from read_final64 7 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (8 * 4) = finalWords64[8]! from read_final64 8 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (9 * 4) = finalWords64[9]! from read_final64 9 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (10 * 4) = finalWords64[10]! from read_final64 10 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (11 * 4) = finalWords64[11]! from read_final64 11 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (12 * 4) = finalWords64[12]! from read_final64 12 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (13 * 4) = finalWords64[13]! from read_final64 13 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (14 * 4) = finalWords64[14]! from read_final64 14 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock64 (15 * 4) = finalWords64[15]! from read_final64 15 (by omega)]
  decide

theorem compress_final64 (h : Array UInt32) :
    Ripemd160.compressBlock h finalBlock64 0 =
      CompressionCorrect.normalizedCompress h finalWords64 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule_final64]

theorem stepFinal :
    CompressionCorrect.normalizedCompress PatternedDigest.H1 finalWords64 = state64 := by
  decide

/-- `RIPEMD-160(patterned 64)`. -/
def digest64 : ByteArray := ByteArray.mk #[
  0x8a, 0x14, 0xb0, 0xc8, 0x92, 0x87, 0xb3, 0x9b, 0x1a, 0x2f,
  0x73, 0xaa, 0x79, 0xa1, 0xce, 0x95, 0xb0, 0x4e, 0x78, 0x17]

theorem readPadded_input64 (off : Nat) (hoff : off + 32 ≤ 64) (target : ByteArray)
    (hsize : target.size = 32)
    (hbytes : ∀ j (_hj : j < 32) (hs : off + j < input64.size) (ht : j < target.size),
      input64[off + j]'hs = target[j]'ht) :
    EvmSemantics.MachineState.readPadded input64 off 32 = target := by
  apply ByteArray.ext_getElem
  · rw [Challenge.EvmProof.Memory.readPadded_size, hsize]
  · intro j hj₁ hj₂
    have hj : j < 32 := by
      rw [Challenge.EvmProof.Memory.readPadded_size] at hj₁
      exact hj₁
    have hsource : off + j < input64.size := by rw [input64_size]; omega
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hj₁,
      Challenge.EvmProof.Memory.readPadded_getElem?_getD]
    rw [if_pos hj, Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hsource]
    exact hbytes j hj hsource hj₂

theorem word0_input64 :
    EvmSemantics.MachineState.readWord input64 0 = PatternedWordData.expectedWordAt 0 := by
  rw [PatternedWordData.expectedWordAt_0]
  unfold EvmSemantics.MachineState.readWord
  rw [readPadded_input64 0 (by omega) (ByteArray.mk #[
      0x07, 0x2c, 0x51, 0x76, 0x9b, 0xc0, 0xe5, 0x0a, 0x2f, 0x54,
      0x79, 0x9e, 0xc3, 0xe8, 0x0d, 0x32, 0x57, 0x7c, 0xa1, 0xc6,
      0xeb, 0x10, 0x35, 0x5a, 0x7f, 0xa4, 0xc9, 0xee, 0x13, 0x38,
      0x5d, 0x82]) (by decide) (by intro j _hj hs ht; interval_cases j <;> rfl)]
  apply Challenge.EvmProof.Word.word_ext
  norm_num [EvmSemantics.Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data, List.foldl,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt8.toNat_ofNat]
  decide

theorem word1_input64 :
    EvmSemantics.MachineState.readWord input64 32 = PatternedWordData.expectedWordAt 1 := by
  rw [PatternedWordData.expectedWordAt_1]
  unfold EvmSemantics.MachineState.readWord
  rw [readPadded_input64 32 (by omega) (ByteArray.mk #[
      0xa7, 0xcc, 0xf1, 0x16, 0x3b, 0x60, 0x85, 0xaa, 0xcf, 0xf4,
      0x19, 0x3e, 0x63, 0x88, 0xad, 0xd2, 0xf7, 0x1c, 0x41, 0x66,
      0x8b, 0xb0, 0xd5, 0xfa, 0x1f, 0x44, 0x69, 0x8e, 0xb3, 0xd8,
      0xfd, 0x22]) (by decide) (by intro j _hj hs ht; interval_cases j <;> rfl)]
  apply Challenge.EvmProof.Word.word_ext
  norm_num [EvmSemantics.Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data, List.foldl,
    Challenge.EvmProof.Word.word_toNat_ofNat, UInt8.toNat_ofNat]
  decide

theorem block0_input64 :
    Ripemd160.compressBlock PatternedDigest.H0 (Padding.paddedMessage input64) 0 =
      PatternedDigest.H1 :=
  PrefixStateData.h8_firstBlock input64 word0_input64 word1_input64

theorem block1_input64 :
    Ripemd160.compressBlock PatternedDigest.H1 (Padding.paddedMessage input64) 64 =
      state64 := by
  rw [HashSpecBridge.paddedMessage_eq_prefix_tail]
  have hprefix : (HashSpecBridge.fullPrefix input64).size = 64 := by
    simp [HashSpecBridge.fullPrefix, input64_size]
  have hright := HashSpecBridge.compressBlock_append_right PatternedDigest.H1
    (HashSpecBridge.fullPrefix input64) (HashSpecBridge.canonicalTail input64) 0
  rw [hprefix] at hright
  norm_num at hright
  rw [hright, canonicalTail_input64, compress_final64, stepFinal]

theorem hash_input64 : Ripemd160.hash input64 = digest64 := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  unfold SpecBridge.paddedHash
  have hlen : Padding.paddedLength input64.size / 64 = 2 := by
    rw [input64_size]; decide
  rw [hlen, show (2 : Nat) = 1 + 1 from rfl, SpecBridge.absorbBlocks_succ,
    show (1 : Nat) = 0 + 1 from rfl, SpecBridge.absorbBlocks_succ,
    SpecBridge.absorbBlocks_zero]
  norm_num
  rw [show (Ripemd160.H0 : Array UInt32) = PatternedDigest.H0 from rfl, block0_input64,
    block1_input64]
  unfold SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push, state64, digest64]
  decide

theorem word2_input64_ne :
    EvmSemantics.MachineState.readWord input64 64 ≠ PatternedWordData.expectedWordAt 2 := by
  have hread : EvmSemantics.MachineState.readPadded input64 64 32 =
      ByteArray.mk (Array.replicate 32 (0 : UInt8)) := by
    apply ByteArray.ext_getElem
    · rw [Challenge.EvmProof.Memory.readPadded_size]
      norm_num [ByteArray.size]
    · intro j hj₁ hj₂
      have hj : j < 32 := by
        rw [Challenge.EvmProof.Memory.readPadded_size] at hj₁
        exact hj₁
      have hsource : input64.size ≤ 64 + j := by
        rw [input64_size]; omega
      rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hj₁,
        Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos hj,
        Challenge.EvmProof.Memory.getElem?_getD_eq_zero_of_size_le _ _ hsource]
      change (0 : UInt8) = (Array.replicate 32 (0 : UInt8))[j]
      rw [Array.getElem_replicate]
  rw [PatternedWordData.expectedWordAt_2]
  unfold EvmSemantics.MachineState.readWord
  rw [hread]
  intro h
  have hval := congrArg EvmSemantics.UInt256.toNat h
  revert hval
  have hzero : UInt8.toNat (0 : UInt8) = 0 := by decide
  norm_num [EvmSemantics.Data.Bytes.bytesToBigEndianNat,
    Challenge.EvmProof.Bytecode.toList_eq_data, Array.toList_replicate,
    List.replicate_succ, List.foldl, hzero,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Exact64Digest
