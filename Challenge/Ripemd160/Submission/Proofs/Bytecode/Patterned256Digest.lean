import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Data
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
set_option linter.unnecessarySeqFocus false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Digest
open EvmSemantics EvmSemantics.Crypto
open Patterned256Data
def zeroLiteral : ByteArray := ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
def lengthLiteral : ByteArray := ByteArray.mk #[0x00, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
def finalTail : ByteArray := ByteArray.mk #[0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
def tailWords0 : Array UInt32 := #[0x80, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x800, 0x0]
def finalHash : Array UInt32 := #[0x463cc5c6, 0x1cde08cf, 0x5ab17553, 0x2d6a67f8, 0x8a52ef32]
def targetDigest : ByteArray := SpecBridge.emitDigest finalHash
def paddedDigest : ByteArray := ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc6, 0xc5, 0x3c, 0x46, 0xcf, 0x08, 0xde, 0x1c, 0x53, 0x75, 0xb1, 0x5a, 0xf8, 0x67, 0x6a, 0x2d, 0x32, 0xef, 0x52, 0x8a]
def paddedDigestWord : UInt256 := 0xc6c53c46cf08de1c5375b15af8676a2d32ef528a

@[simp] theorem finalTail_size : finalTail.size = 64 := by decide

private theorem zeroBytes_eq_literal : Padding.zeroBytes 256 = zeroLiteral := by
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
  change data.extract 256 256 ++ ByteArray.mk #[0x80] ++ Padding.zeroBytes 256 ++
    Padding.lengthBytes data = finalTail
  have he : data.extract 256 256 = ByteArray.empty := by
    apply ByteArray.ext_getElem
    · simp
    · intro i hi hj
      simp at hj
  rw [he, zeroBytes_eq_literal, lengthBytes_eq_literal]
  decide

private theorem compress_data (h : Array UInt32) (off : Nat) (hoff : off + 64 ≤ 256) :
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

theorem hashAfter_four : SpecBridge.absorbBlocks Ripemd160.H0 data 0 4 =
    PatternedDigest.H4 := by
  change Ripemd160.compressBlock
    (Ripemd160.compressBlock
      (Ripemd160.compressBlock
        (Ripemd160.compressBlock PatternedDigest.H0 data 0) data 64) data 128)
      data 192 = PatternedDigest.H4
  rw [compress_data _ 0 (by omega), compress_data _ 64 (by omega),
    compress_data _ 128 (by omega), compress_data _ 192 (by omega)]
  simp only [CompressionCorrect.compressBlock_eq_normalized,
    PatternedDigest.schedule0, PatternedDigest.schedule1, PatternedDigest.schedule2,
    PatternedDigest.schedule3, PatternedDigestA.step0, PatternedDigestA.step1,
    PatternedDigestA.step2, PatternedDigestA.step3]

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

theorem step_tail : CompressionCorrect.normalizedCompress PatternedDigest.H4 tailWords0 =
    finalHash := by decide

theorem hash_data_eq : Ripemd160.hash data = targetDigest := by
  rw [HashSpecBridge.hash_eq_two_phase, data_size, canonicalTail_eq_literal]
  change SpecBridge.emitDigest
    (SpecBridge.absorbBlocks (SpecBridge.absorbBlocks Ripemd160.H0 data 0 4)
      finalTail 0 1) = targetDigest
  rw [hashAfter_four]
  change SpecBridge.emitDigest
    (Ripemd160.compressBlock PatternedDigest.H4 finalTail 0) = targetDigest
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule_tail0, step_tail]
  rfl

theorem targetDigest_eq_literal : targetDigest = ByteArray.mk #[0xc6, 0xc5, 0x3c, 0x46, 0xcf, 0x08, 0xde, 0x1c, 0x53, 0x75, 0xb1, 0x5a, 0xf8, 0x67, 0x6a, 0x2d, 0x32, 0xef, 0x52, 0x8a] := by
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Digest

#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Digest.spec_data_eq
