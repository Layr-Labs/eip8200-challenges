import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData


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

theorem compress_final (h : Array UInt32) :
    Ripemd160.compressBlock h finalBlock 0 =
      CompressionCorrect.normalizedCompress h finalWords := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule_final]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
