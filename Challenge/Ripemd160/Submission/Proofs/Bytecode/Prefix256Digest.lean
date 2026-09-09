import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Data


set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
set_option linter.unnecessarySeqFocus false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Digest
open EvmSemantics EvmSemantics.Crypto
open Prefix256Data

def tailMessage : ByteArray := ByteArray.mk #[0x52, 0x77, 0x9c, 0xc1, 0xe6, 0x0b, 0x30, 0x55, 0x7a, 0x9f, 0xc4, 0xe9, 0x0e, 0x33, 0x58, 0x7d, 0xa2, 0xc7, 0xec, 0x11, 0x36, 0x5b, 0x80, 0xa5, 0xca, 0xef, 0x14, 0x39, 0x5e, 0x83, 0xa8, 0xcd, 0xf2, 0x17, 0x3c, 0x61, 0x86, 0xab, 0xd0, 0xf5, 0x1a, 0x3f, 0x64, 0x89, 0xae, 0xd3, 0xf8, 0x1d, 0x42, 0x67, 0x8c, 0xb1, 0xd6, 0xfb, 0x20, 0x45]
def zeroLiteral : ByteArray := ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
def lengthLiteral : ByteArray := ByteArray.mk #[0xc0, 0x0b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
def finalTail : ByteArray := ByteArray.mk #[0x52, 0x77, 0x9c, 0xc1, 0xe6, 0x0b, 0x30, 0x55, 0x7a, 0x9f, 0xc4, 0xe9, 0x0e, 0x33, 0x58, 0x7d, 0xa2, 0xc7, 0xec, 0x11, 0x36, 0x5b, 0x80, 0xa5, 0xca, 0xef, 0x14, 0x39, 0x5e, 0x83, 0xa8, 0xcd, 0xf2, 0x17, 0x3c, 0x61, 0x86, 0xab, 0xd0, 0xf5, 0x1a, 0x3f, 0x64, 0x89, 0xae, 0xd3, 0xf8, 0x1d, 0x42, 0x67, 0x8c, 0xb1, 0xd6, 0xfb, 0x20, 0x45, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc0, 0x0b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
def tailWords0 : Array UInt32 := #[0xc19c7752, 0x55300be6, 0xe9c49f7a, 0x7d58330e, 0x11ecc7a2, 0xa5805b36, 0x3914efca, 0xcda8835e, 0x613c17f2, 0xf5d0ab86, 0x89643f1a, 0x1df8d3ae, 0xb18c6742, 0x4520fbd6, 0x00000080, 0x00000000]
def tailWords1 : Array UInt32 := #[0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000bc0, 0x00000000]
def finalHash : Array UInt32 := #[0xd2a8cef6, 0xdcf591a4, 0xf7a16a27, 0x7a4d8b61, 0xadc42e55]
def targetDigest : ByteArray := SpecBridge.emitDigest finalHash
def paddedDigest : ByteArray := ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf6, 0xce, 0xa8, 0xd2, 0xa4, 0x91, 0xf5, 0xdc, 0x27, 0x6a, 0xa1, 0xf7, 0x61, 0x8b, 0x4d, 0x7a, 0x55, 0x2e, 0xc4, 0xad]
def paddedDigestWord : UInt256 := 0x000000000000000000000000f6cea8d2a491f5dc276aa1f7618b4d7a552ec4ad

@[simp] theorem finalTail_size : finalTail.size = 128 := by decide

private theorem extract_eq_tailMessage : data.extract 320 376 = tailMessage := by
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract, data_size]
    decide
  · intro i _hleft hright
    have hi : i < 56 := by simpa [tailMessage, ByteArray.size] using hright
    rw [ByteArray.getElem_extract, data_getElem]
    interval_cases i <;>
      norm_num [tailMessage, PatternedInputData.expectedByte,
        ByteArray.getElem_eq_getElem_data, ByteArray.size] <;> decide

private theorem zeroBytes_eq_literal : Padding.zeroBytes 376 = zeroLiteral := by
  unfold Padding.zeroBytes Padding.zeroCount Padding.paddedLength zeroLiteral
  decide

private theorem lengthBytes_eq_literal : Padding.lengthBytes data = lengthLiteral := by
  apply ByteArray.ext_getElem
  · simp only [Padding.lengthBytes, ByteArray.size_ofFn]
    decide
  · intro i hleft _hright
    have hi : i < 8 := by simpa only [Padding.lengthBytes, ByteArray.size_ofFn] using hleft
    rw [Padding.lengthByte data i hi, data_size]
    interval_cases i <;>
      norm_num [lengthLiteral, ByteArray.getElem_eq_getElem_data, ByteArray.size] <;> decide

theorem canonicalTail_eq_literal : HashSpecBridge.canonicalTail data = finalTail := by
  rw [HashSpecBridge.canonicalTail_eq, data_size]
  change data.extract 320 376 ++ ByteArray.mk #[0x80] ++ Padding.zeroBytes 376 ++
    Padding.lengthBytes data = finalTail
  rw [extract_eq_tailMessage, zeroBytes_eq_literal, lengthBytes_eq_literal]
  decide

private theorem compress_data (h : Array UInt32) (off : Nat) (hoff : off + 64 ≤ 376) :
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

theorem hashAfter_five : SpecBridge.absorbBlocks Ripemd160.H0 data 0 5 =
    PatternedDigest.H5 := by
  change Ripemd160.compressBlock
    (Ripemd160.compressBlock
      (Ripemd160.compressBlock
        (Ripemd160.compressBlock
          (Ripemd160.compressBlock PatternedDigest.H0 data 0) data 64) data 128)
        data 192) data 256 = PatternedDigest.H5
  rw [compress_data _ 0 (by omega), compress_data _ 64 (by omega),
    compress_data _ 128 (by omega), compress_data _ 192 (by omega),
    compress_data _ 256 (by omega)]
  simp only [CompressionCorrect.compressBlock_eq_normalized,
    PatternedDigest.schedule0, PatternedDigest.schedule1, PatternedDigest.schedule2,
    PatternedDigest.schedule3, PatternedDigest.schedule4,
    PatternedDigestA.step0, PatternedDigestA.step1, PatternedDigestA.step2,
    PatternedDigestA.step3, PatternedDigestB.step4]

theorem read_tail0 (i : Nat) (hi : i < 16) :
    Ripemd160.readLE32 finalTail (0 + i * 4) = tailWords0[i]! := by
  interval_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [finalTail, tailWords0, Ripemd160.readLE32, List.range', List.foldl,
        ByteArray.size, ByteArray.getElem_eq_getElem_data] <;>
    try (apply UInt32.eq_of_toBitVec_eq; decide)

theorem schedule_tail0 : CompressionCorrect.schedule finalTail 0 = tailWords0 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 finalTail (0 + 0 * 4) = tailWords0[0]! from read_tail0 0 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 1 * 4) = tailWords0[1]! from read_tail0 1 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 2 * 4) = tailWords0[2]! from read_tail0 2 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 3 * 4) = tailWords0[3]! from read_tail0 3 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 4 * 4) = tailWords0[4]! from read_tail0 4 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 5 * 4) = tailWords0[5]! from read_tail0 5 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 6 * 4) = tailWords0[6]! from read_tail0 6 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 7 * 4) = tailWords0[7]! from read_tail0 7 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 8 * 4) = tailWords0[8]! from read_tail0 8 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 9 * 4) = tailWords0[9]! from read_tail0 9 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 10 * 4) = tailWords0[10]! from read_tail0 10 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 11 * 4) = tailWords0[11]! from read_tail0 11 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 12 * 4) = tailWords0[12]! from read_tail0 12 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 13 * 4) = tailWords0[13]! from read_tail0 13 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 14 * 4) = tailWords0[14]! from read_tail0 14 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (0 + 15 * 4) = tailWords0[15]! from read_tail0 15 (by omega)]
  decide

theorem read_tail1 (i : Nat) (hi : i < 16) :
    Ripemd160.readLE32 finalTail (64 + i * 4) = tailWords1[i]! := by
  interval_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [finalTail, tailWords1, Ripemd160.readLE32, List.range', List.foldl,
        ByteArray.size, ByteArray.getElem_eq_getElem_data] <;>
    try (apply UInt32.eq_of_toBitVec_eq; decide)

theorem schedule_tail1 : CompressionCorrect.schedule finalTail 64 = tailWords1 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 finalTail (64 + 0 * 4) = tailWords1[0]! from read_tail1 0 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 1 * 4) = tailWords1[1]! from read_tail1 1 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 2 * 4) = tailWords1[2]! from read_tail1 2 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 3 * 4) = tailWords1[3]! from read_tail1 3 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 4 * 4) = tailWords1[4]! from read_tail1 4 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 5 * 4) = tailWords1[5]! from read_tail1 5 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 6 * 4) = tailWords1[6]! from read_tail1 6 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 7 * 4) = tailWords1[7]! from read_tail1 7 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 8 * 4) = tailWords1[8]! from read_tail1 8 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 9 * 4) = tailWords1[9]! from read_tail1 9 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 10 * 4) = tailWords1[10]! from read_tail1 10 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 11 * 4) = tailWords1[11]! from read_tail1 11 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 12 * 4) = tailWords1[12]! from read_tail1 12 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 13 * 4) = tailWords1[13]! from read_tail1 13 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 14 * 4) = tailWords1[14]! from read_tail1 14 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (64 + 15 * 4) = tailWords1[15]! from read_tail1 15 (by omega)]
  decide

theorem step_tail : CompressionCorrect.normalizedCompress
    (CompressionCorrect.normalizedCompress PatternedDigest.H5 tailWords0) tailWords1 =
      finalHash := by decide

theorem hash_data_eq : Ripemd160.hash data = targetDigest := by
  rw [HashSpecBridge.hash_eq_two_phase, data_size, canonicalTail_eq_literal]
  change SpecBridge.emitDigest
    (SpecBridge.absorbBlocks (SpecBridge.absorbBlocks Ripemd160.H0 data 0 5)
      finalTail 0 2) = targetDigest
  rw [hashAfter_five]
  change SpecBridge.emitDigest
    (Ripemd160.compressBlock (Ripemd160.compressBlock PatternedDigest.H5 finalTail 0)
      finalTail 64) = targetDigest
  rw [CompressionCorrect.compressBlock_eq_normalized,
    CompressionCorrect.compressBlock_eq_normalized, schedule_tail0, schedule_tail1,
    step_tail]
  rfl

theorem targetDigest_eq_literal : targetDigest = ByteArray.mk #[0xf6, 0xce, 0xa8, 0xd2, 0xa4, 0x91, 0xf5, 0xdc, 0x27, 0x6a, 0xa1, 0xf7, 0x61, 0x8b, 0x4d, 0x7a, 0x55, 0x2e, 0xc4, 0xad] := by
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Digest

#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Digest.spec_data_eq
