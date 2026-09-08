import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Data
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSchedulesA

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Digest

open EvmSemantics EvmSemantics.Crypto
open Prefix128Data

def finalWords : Array UInt32 :=
  #[0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1024, 0]

def finalHash : Array UInt32 :=
  #[0x14afdf28, 0xf45399ed, 0x56bb7a9c, 0xc6d00813, 0x79c1c44b]

def targetDigest : ByteArray := SpecBridge.emitDigest finalHash

def paddedDigest : ByteArray := ByteArray.mk #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0x28, 0xdf, 0xaf, 0x14, 0xed, 0x99, 0x53, 0xf4, 0x9c, 0x7a,
  0xbb, 0x56, 0x13, 0x08, 0xd0, 0xc6, 0x4b, 0xc4, 0xc1, 0x79]

def paddedDigestWord : UInt256 :=
  0x00000000000000000000000028dfaf14ed9953f49c7abb561308d0c64bc4c179

def finalBlock : ByteArray := ByteArray.mk #[
  0x80, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 4, 0, 0, 0, 0, 0, 0]

@[simp] theorem finalBlock_size : finalBlock.size = 64 := by decide

private theorem lengthBytes_eq :
    Padding.lengthBytes data = ByteArray.mk #[0, 4, 0, 0, 0, 0, 0, 0] := by
  apply ByteArray.ext_getElem
  · rw [Padding.lengthBytes_size]
    decide
  · intro i hleft _hright
    have hi : i < 8 := by simpa only [Padding.lengthBytes_size] using hleft
    rw [Padding.lengthByte data i hi, data_size]
    interval_cases i <;>
      norm_num [ByteArray.getElem_eq_getElem_data, ByteArray.size] <;>
      decide

theorem paddedMessage_split : Padding.paddedMessage data = data ++ finalBlock := by
  unfold Padding.paddedMessage
  rw [data_size, lengthBytes_eq]
  simp only [ByteArray.append_assoc]
  rfl

private theorem compress_data (h : Array UInt32) (off : Nat) (hoff : off + 64 ≤ 128) :
    Ripemd160.compressBlock h data off =
      Ripemd160.compressBlock h PatternedInputData.patternedInput off := by
  apply HashSpecBridge.compressBlock_eq_of_readLE32
  intro i hi
  apply HashSpecBridge.readLE32_eq_of_byte
  intro j hj
  have hdata : off + i * 4 + j < data.size := by rw [data_size]; omega
  have hpattern : off + i * 4 + j < PatternedInputData.patternedInput.size := by
    rw [PatternedInputData.patternedInput_size]; omega
  rw [dif_pos hdata, dif_pos hpattern,
    data_getElem, PatternedInputData.patternedInput_getElem]

theorem hashAfter_two : SpecBridge.absorbBlocks Ripemd160.H0 data 0 2 =
    PatternedDigest.H2 := by
  change Ripemd160.compressBlock
    (Ripemd160.compressBlock PatternedDigest.H0 data 0) data 64 =
      PatternedDigest.H2
  rw [compress_data _ 0 (by omega), compress_data _ 64 (by omega)]
  simp only [CompressionCorrect.compressBlock_eq_normalized,
    PatternedDigest.schedule0, PatternedDigest.schedule1,
    PatternedDigestA.step0, PatternedDigestA.step1]

theorem read_final (i : Nat) (hi : i < 16) :
    Ripemd160.readLE32 finalBlock (i * 4) = finalWords[i]! := by
  interval_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [finalBlock, finalWords, Ripemd160.readLE32,
        List.range', List.foldl, ByteArray.size,
        ByteArray.getElem_eq_getElem_data] <;>
    try (apply UInt32.eq_of_toBitVec_eq; decide)

theorem schedule_final : CompressionCorrect.schedule finalBlock 0 = finalWords := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 finalBlock (0 * 4) = finalWords[0]! from read_final 0 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (1 * 4) = finalWords[1]! from read_final 1 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (2 * 4) = finalWords[2]! from read_final 2 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (3 * 4) = finalWords[3]! from read_final 3 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (4 * 4) = finalWords[4]! from read_final 4 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (5 * 4) = finalWords[5]! from read_final 5 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (6 * 4) = finalWords[6]! from read_final 6 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (7 * 4) = finalWords[7]! from read_final 7 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (8 * 4) = finalWords[8]! from read_final 8 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (9 * 4) = finalWords[9]! from read_final 9 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (10 * 4) = finalWords[10]! from read_final 10 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (11 * 4) = finalWords[11]! from read_final 11 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (12 * 4) = finalWords[12]! from read_final 12 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (13 * 4) = finalWords[13]! from read_final 13 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (14 * 4) = finalWords[14]! from read_final 14 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (15 * 4) = finalWords[15]! from read_final 15 (by omega)]
  decide

theorem step_final :
    CompressionCorrect.normalizedCompress PatternedDigest.H2 finalWords = finalHash := by
  decide

theorem hashAfter_three :
    SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data) 0 3 =
      finalHash := by
  rw [paddedMessage_split]
  rw [show 3 = 2 + 1 from rfl,
    HashSpecBridge.absorbBlocks_append Ripemd160.H0 data finalBlock 2 1 (by
      rw [data_size]), hashAfter_two]
  change Ripemd160.compressBlock PatternedDigest.H2 finalBlock 0 = finalHash
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule_final, step_final]

theorem targetDigest_eq_literal : targetDigest = ByteArray.mk #[
    0x28, 0xdf, 0xaf, 0x14, 0xed, 0x99, 0x53, 0xf4, 0x9c, 0x7a,
    0xbb, 0x56, 0x13, 0x08, 0xd0, 0xc6, 0x4b, 0xc4, 0xc1, 0x79] := by
  unfold targetDigest SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

@[simp] theorem targetDigest_size : targetDigest.size = 20 := by
  rw [targetDigest_eq_literal]
  decide

@[simp] theorem paddedDigest_size : paddedDigest.size = 32 := by decide

theorem hash_data_eq : Ripemd160.hash data = targetDigest := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  unfold SpecBridge.paddedHash
  rw [data_size]
  change SpecBridge.emitDigest
    (SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data) 0 3) = targetDigest
  rw [hashAfter_three]
  rfl

theorem spec_data_eq : Challenge.Ripemd160.spec data = paddedDigest := by
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [hash_data_eq, targetDigest_eq_literal]
  decide

theorem wordBytes_eq_paddedDigest :
    Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32 = paddedDigest := by
  rw [Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Digest
