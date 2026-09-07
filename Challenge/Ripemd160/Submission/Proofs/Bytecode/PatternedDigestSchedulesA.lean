import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestReadSchedule

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem schedule0 : CompressionCorrect.schedule patternedInput 0 = block0 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (0 + 0 * 4) =
      expectedWord (0 + 0 * 4) from
        read_patterned 0 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 1 * 4) =
      expectedWord (0 + 1 * 4) from
        read_patterned 0 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 2 * 4) =
      expectedWord (0 + 2 * 4) from
        read_patterned 0 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 3 * 4) =
      expectedWord (0 + 3 * 4) from
        read_patterned 0 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 4 * 4) =
      expectedWord (0 + 4 * 4) from
        read_patterned 0 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 5 * 4) =
      expectedWord (0 + 5 * 4) from
        read_patterned 0 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 6 * 4) =
      expectedWord (0 + 6 * 4) from
        read_patterned 0 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 7 * 4) =
      expectedWord (0 + 7 * 4) from
        read_patterned 0 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 8 * 4) =
      expectedWord (0 + 8 * 4) from
        read_patterned 0 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 9 * 4) =
      expectedWord (0 + 9 * 4) from
        read_patterned 0 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 10 * 4) =
      expectedWord (0 + 10 * 4) from
        read_patterned 0 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 11 * 4) =
      expectedWord (0 + 11 * 4) from
        read_patterned 0 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 12 * 4) =
      expectedWord (0 + 12 * 4) from
        read_patterned 0 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 13 * 4) =
      expectedWord (0 + 13 * 4) from
        read_patterned 0 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 14 * 4) =
      expectedWord (0 + 14 * 4) from
        read_patterned 0 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (0 + 15 * 4) =
      expectedWord (0 + 15 * 4) from
        read_patterned 0 15 (by omega) (by omega)]
  decide

theorem schedule1 : CompressionCorrect.schedule patternedInput 64 = block1 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (64 + 0 * 4) =
      expectedWord (64 + 0 * 4) from
        read_patterned 64 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 1 * 4) =
      expectedWord (64 + 1 * 4) from
        read_patterned 64 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 2 * 4) =
      expectedWord (64 + 2 * 4) from
        read_patterned 64 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 3 * 4) =
      expectedWord (64 + 3 * 4) from
        read_patterned 64 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 4 * 4) =
      expectedWord (64 + 4 * 4) from
        read_patterned 64 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 5 * 4) =
      expectedWord (64 + 5 * 4) from
        read_patterned 64 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 6 * 4) =
      expectedWord (64 + 6 * 4) from
        read_patterned 64 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 7 * 4) =
      expectedWord (64 + 7 * 4) from
        read_patterned 64 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 8 * 4) =
      expectedWord (64 + 8 * 4) from
        read_patterned 64 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 9 * 4) =
      expectedWord (64 + 9 * 4) from
        read_patterned 64 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 10 * 4) =
      expectedWord (64 + 10 * 4) from
        read_patterned 64 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 11 * 4) =
      expectedWord (64 + 11 * 4) from
        read_patterned 64 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 12 * 4) =
      expectedWord (64 + 12 * 4) from
        read_patterned 64 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 13 * 4) =
      expectedWord (64 + 13 * 4) from
        read_patterned 64 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 14 * 4) =
      expectedWord (64 + 14 * 4) from
        read_patterned 64 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (64 + 15 * 4) =
      expectedWord (64 + 15 * 4) from
        read_patterned 64 15 (by omega) (by omega)]
  decide

theorem schedule2 : CompressionCorrect.schedule patternedInput 128 = block2 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (128 + 0 * 4) =
      expectedWord (128 + 0 * 4) from
        read_patterned 128 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 1 * 4) =
      expectedWord (128 + 1 * 4) from
        read_patterned 128 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 2 * 4) =
      expectedWord (128 + 2 * 4) from
        read_patterned 128 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 3 * 4) =
      expectedWord (128 + 3 * 4) from
        read_patterned 128 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 4 * 4) =
      expectedWord (128 + 4 * 4) from
        read_patterned 128 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 5 * 4) =
      expectedWord (128 + 5 * 4) from
        read_patterned 128 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 6 * 4) =
      expectedWord (128 + 6 * 4) from
        read_patterned 128 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 7 * 4) =
      expectedWord (128 + 7 * 4) from
        read_patterned 128 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 8 * 4) =
      expectedWord (128 + 8 * 4) from
        read_patterned 128 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 9 * 4) =
      expectedWord (128 + 9 * 4) from
        read_patterned 128 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 10 * 4) =
      expectedWord (128 + 10 * 4) from
        read_patterned 128 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 11 * 4) =
      expectedWord (128 + 11 * 4) from
        read_patterned 128 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 12 * 4) =
      expectedWord (128 + 12 * 4) from
        read_patterned 128 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 13 * 4) =
      expectedWord (128 + 13 * 4) from
        read_patterned 128 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 14 * 4) =
      expectedWord (128 + 14 * 4) from
        read_patterned 128 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (128 + 15 * 4) =
      expectedWord (128 + 15 * 4) from
        read_patterned 128 15 (by omega) (by omega)]
  decide

theorem schedule3 : CompressionCorrect.schedule patternedInput 192 = block3 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (192 + 0 * 4) =
      expectedWord (192 + 0 * 4) from
        read_patterned 192 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 1 * 4) =
      expectedWord (192 + 1 * 4) from
        read_patterned 192 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 2 * 4) =
      expectedWord (192 + 2 * 4) from
        read_patterned 192 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 3 * 4) =
      expectedWord (192 + 3 * 4) from
        read_patterned 192 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 4 * 4) =
      expectedWord (192 + 4 * 4) from
        read_patterned 192 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 5 * 4) =
      expectedWord (192 + 5 * 4) from
        read_patterned 192 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 6 * 4) =
      expectedWord (192 + 6 * 4) from
        read_patterned 192 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 7 * 4) =
      expectedWord (192 + 7 * 4) from
        read_patterned 192 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 8 * 4) =
      expectedWord (192 + 8 * 4) from
        read_patterned 192 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 9 * 4) =
      expectedWord (192 + 9 * 4) from
        read_patterned 192 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 10 * 4) =
      expectedWord (192 + 10 * 4) from
        read_patterned 192 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 11 * 4) =
      expectedWord (192 + 11 * 4) from
        read_patterned 192 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 12 * 4) =
      expectedWord (192 + 12 * 4) from
        read_patterned 192 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 13 * 4) =
      expectedWord (192 + 13 * 4) from
        read_patterned 192 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 14 * 4) =
      expectedWord (192 + 14 * 4) from
        read_patterned 192 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (192 + 15 * 4) =
      expectedWord (192 + 15 * 4) from
        read_patterned 192 15 (by omega) (by omega)]
  decide

theorem schedule4 : CompressionCorrect.schedule patternedInput 256 = block4 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (256 + 0 * 4) =
      expectedWord (256 + 0 * 4) from
        read_patterned 256 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 1 * 4) =
      expectedWord (256 + 1 * 4) from
        read_patterned 256 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 2 * 4) =
      expectedWord (256 + 2 * 4) from
        read_patterned 256 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 3 * 4) =
      expectedWord (256 + 3 * 4) from
        read_patterned 256 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 4 * 4) =
      expectedWord (256 + 4 * 4) from
        read_patterned 256 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 5 * 4) =
      expectedWord (256 + 5 * 4) from
        read_patterned 256 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 6 * 4) =
      expectedWord (256 + 6 * 4) from
        read_patterned 256 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 7 * 4) =
      expectedWord (256 + 7 * 4) from
        read_patterned 256 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 8 * 4) =
      expectedWord (256 + 8 * 4) from
        read_patterned 256 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 9 * 4) =
      expectedWord (256 + 9 * 4) from
        read_patterned 256 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 10 * 4) =
      expectedWord (256 + 10 * 4) from
        read_patterned 256 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 11 * 4) =
      expectedWord (256 + 11 * 4) from
        read_patterned 256 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 12 * 4) =
      expectedWord (256 + 12 * 4) from
        read_patterned 256 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 13 * 4) =
      expectedWord (256 + 13 * 4) from
        read_patterned 256 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 14 * 4) =
      expectedWord (256 + 14 * 4) from
        read_patterned 256 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (256 + 15 * 4) =
      expectedWord (256 + 15 * 4) from
        read_patterned 256 15 (by omega) (by omega)]
  decide


end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
