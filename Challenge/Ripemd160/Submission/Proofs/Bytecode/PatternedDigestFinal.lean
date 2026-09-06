import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestD

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

private def tailLiteral : ByteArray := ByteArray.mk #[
  0xe8, 0x0d, 0x32, 0x57, 0x7c, 0xa1, 0xc6, 0xeb,
  0x10, 0x35, 0x5a, 0x7f, 0xa4, 0xc9, 0xee, 0x13,
  0x38, 0x5d, 0x82, 0xa7, 0xcc, 0xf1, 0x16, 0x3b,
  0x60, 0x85, 0xaa, 0xcf, 0xf4, 0x19, 0x3e, 0x63,
  0x88, 0xad, 0xd2, 0xf7, 0x1c, 0x41, 0x66, 0x8b]

private theorem tailLiteral_size : tailLiteral.size = 40 := by decide

private theorem extract_eq_tail : patternedInput.extract 960 1000 = tailLiteral := by
  apply ByteArray.ext_getElem
  · simp [patternedInput_size, tailLiteral_size]
  · intro i hleft hright
    have hi : i < 40 := by
      simpa [tailLiteral_size] using hright
    rw [ByteArray.getElem_extract]
    rw [patternedInput_getElem]
    interval_cases i <;>
      norm_num [tailLiteral, expectedByte,
        ByteArray.getElem_eq_getElem_data, ByteArray.size] <;>
      decide

private def zerosLiteral : ByteArray := ByteArray.mk #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem zeroBytes_eq_zeros : Padding.zeroBytes 1000 = zerosLiteral := by
  unfold Padding.zeroBytes Padding.zeroCount Padding.paddedLength zerosLiteral
  decide

private def lengthLiteral : ByteArray := ByteArray.mk #[
  0x40, 0x1f, 0, 0, 0, 0, 0, 0]

private theorem lengthBytes_eq_length :
    Padding.lengthBytes patternedInput = lengthLiteral := by
  apply ByteArray.ext_getElem
  · rw [show (Padding.lengthBytes patternedInput).size = 8 by
      simp only [Padding.lengthBytes, ByteArray.size_ofFn]]
    decide
  · intro i hleft _hright
    have hi : i < 8 := by
      simpa only [Padding.lengthBytes, ByteArray.size_ofFn] using hleft
    rw [Padding.lengthByte patternedInput i hi, patternedInput_size]
    interval_cases i <;>
      norm_num [lengthLiteral, ByteArray.getElem_eq_getElem_data,
        ByteArray.size] <;>
      decide

private def finalBlockLiteral : ByteArray := ByteArray.mk #[
  0xe8, 0x0d, 0x32, 0x57, 0x7c, 0xa1, 0xc6, 0xeb,
  0x10, 0x35, 0x5a, 0x7f, 0xa4, 0xc9, 0xee, 0x13,
  0x38, 0x5d, 0x82, 0xa7, 0xcc, 0xf1, 0x16, 0x3b,
  0x60, 0x85, 0xaa, 0xcf, 0xf4, 0x19, 0x3e, 0x63,
  0x88, 0xad, 0xd2, 0xf7, 0x1c, 0x41, 0x66, 0x8b,
  0x80, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0x40, 0x1f, 0, 0, 0, 0, 0, 0]

private theorem finalBlock_eq_literal : finalBlock = finalBlockLiteral := by
  unfold finalBlock
  rw [extract_eq_tail, zeroBytes_eq_zeros, lengthBytes_eq_length]
  unfold tailLiteral zerosLiteral lengthLiteral finalBlockLiteral
  decide

theorem read_final (i : Nat) (hi : i < 16) :
    Ripemd160.readLE32 finalBlock (i * 4) = finalWords[i]! := by
  rw [finalBlock_eq_literal]
  interval_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [finalBlockLiteral, finalWords, Ripemd160.readLE32,
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
