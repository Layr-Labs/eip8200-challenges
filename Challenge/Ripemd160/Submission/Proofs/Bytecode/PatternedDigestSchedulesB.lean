import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSchedulesA

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem schedule5 : CompressionCorrect.schedule patternedInput 320 = block5 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (320 + 0 * 4) =
      expectedWord (320 + 0 * 4) from
        read_patterned 320 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 1 * 4) =
      expectedWord (320 + 1 * 4) from
        read_patterned 320 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 2 * 4) =
      expectedWord (320 + 2 * 4) from
        read_patterned 320 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 3 * 4) =
      expectedWord (320 + 3 * 4) from
        read_patterned 320 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 4 * 4) =
      expectedWord (320 + 4 * 4) from
        read_patterned 320 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 5 * 4) =
      expectedWord (320 + 5 * 4) from
        read_patterned 320 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 6 * 4) =
      expectedWord (320 + 6 * 4) from
        read_patterned 320 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 7 * 4) =
      expectedWord (320 + 7 * 4) from
        read_patterned 320 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 8 * 4) =
      expectedWord (320 + 8 * 4) from
        read_patterned 320 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 9 * 4) =
      expectedWord (320 + 9 * 4) from
        read_patterned 320 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 10 * 4) =
      expectedWord (320 + 10 * 4) from
        read_patterned 320 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 11 * 4) =
      expectedWord (320 + 11 * 4) from
        read_patterned 320 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 12 * 4) =
      expectedWord (320 + 12 * 4) from
        read_patterned 320 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 13 * 4) =
      expectedWord (320 + 13 * 4) from
        read_patterned 320 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 14 * 4) =
      expectedWord (320 + 14 * 4) from
        read_patterned 320 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (320 + 15 * 4) =
      expectedWord (320 + 15 * 4) from
        read_patterned 320 15 (by omega) (by omega)]
  decide

theorem schedule6 : CompressionCorrect.schedule patternedInput 384 = block6 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (384 + 0 * 4) =
      expectedWord (384 + 0 * 4) from
        read_patterned 384 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 1 * 4) =
      expectedWord (384 + 1 * 4) from
        read_patterned 384 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 2 * 4) =
      expectedWord (384 + 2 * 4) from
        read_patterned 384 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 3 * 4) =
      expectedWord (384 + 3 * 4) from
        read_patterned 384 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 4 * 4) =
      expectedWord (384 + 4 * 4) from
        read_patterned 384 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 5 * 4) =
      expectedWord (384 + 5 * 4) from
        read_patterned 384 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 6 * 4) =
      expectedWord (384 + 6 * 4) from
        read_patterned 384 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 7 * 4) =
      expectedWord (384 + 7 * 4) from
        read_patterned 384 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 8 * 4) =
      expectedWord (384 + 8 * 4) from
        read_patterned 384 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 9 * 4) =
      expectedWord (384 + 9 * 4) from
        read_patterned 384 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 10 * 4) =
      expectedWord (384 + 10 * 4) from
        read_patterned 384 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 11 * 4) =
      expectedWord (384 + 11 * 4) from
        read_patterned 384 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 12 * 4) =
      expectedWord (384 + 12 * 4) from
        read_patterned 384 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 13 * 4) =
      expectedWord (384 + 13 * 4) from
        read_patterned 384 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 14 * 4) =
      expectedWord (384 + 14 * 4) from
        read_patterned 384 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (384 + 15 * 4) =
      expectedWord (384 + 15 * 4) from
        read_patterned 384 15 (by omega) (by omega)]
  decide

theorem schedule7 : CompressionCorrect.schedule patternedInput 448 = block7 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (448 + 0 * 4) =
      expectedWord (448 + 0 * 4) from
        read_patterned 448 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 1 * 4) =
      expectedWord (448 + 1 * 4) from
        read_patterned 448 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 2 * 4) =
      expectedWord (448 + 2 * 4) from
        read_patterned 448 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 3 * 4) =
      expectedWord (448 + 3 * 4) from
        read_patterned 448 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 4 * 4) =
      expectedWord (448 + 4 * 4) from
        read_patterned 448 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 5 * 4) =
      expectedWord (448 + 5 * 4) from
        read_patterned 448 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 6 * 4) =
      expectedWord (448 + 6 * 4) from
        read_patterned 448 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 7 * 4) =
      expectedWord (448 + 7 * 4) from
        read_patterned 448 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 8 * 4) =
      expectedWord (448 + 8 * 4) from
        read_patterned 448 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 9 * 4) =
      expectedWord (448 + 9 * 4) from
        read_patterned 448 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 10 * 4) =
      expectedWord (448 + 10 * 4) from
        read_patterned 448 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 11 * 4) =
      expectedWord (448 + 11 * 4) from
        read_patterned 448 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 12 * 4) =
      expectedWord (448 + 12 * 4) from
        read_patterned 448 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 13 * 4) =
      expectedWord (448 + 13 * 4) from
        read_patterned 448 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 14 * 4) =
      expectedWord (448 + 14 * 4) from
        read_patterned 448 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (448 + 15 * 4) =
      expectedWord (448 + 15 * 4) from
        read_patterned 448 15 (by omega) (by omega)]
  decide

theorem schedule8 : CompressionCorrect.schedule patternedInput 512 = block8 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (512 + 0 * 4) =
      expectedWord (512 + 0 * 4) from
        read_patterned 512 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 1 * 4) =
      expectedWord (512 + 1 * 4) from
        read_patterned 512 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 2 * 4) =
      expectedWord (512 + 2 * 4) from
        read_patterned 512 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 3 * 4) =
      expectedWord (512 + 3 * 4) from
        read_patterned 512 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 4 * 4) =
      expectedWord (512 + 4 * 4) from
        read_patterned 512 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 5 * 4) =
      expectedWord (512 + 5 * 4) from
        read_patterned 512 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 6 * 4) =
      expectedWord (512 + 6 * 4) from
        read_patterned 512 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 7 * 4) =
      expectedWord (512 + 7 * 4) from
        read_patterned 512 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 8 * 4) =
      expectedWord (512 + 8 * 4) from
        read_patterned 512 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 9 * 4) =
      expectedWord (512 + 9 * 4) from
        read_patterned 512 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 10 * 4) =
      expectedWord (512 + 10 * 4) from
        read_patterned 512 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 11 * 4) =
      expectedWord (512 + 11 * 4) from
        read_patterned 512 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 12 * 4) =
      expectedWord (512 + 12 * 4) from
        read_patterned 512 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 13 * 4) =
      expectedWord (512 + 13 * 4) from
        read_patterned 512 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 14 * 4) =
      expectedWord (512 + 14 * 4) from
        read_patterned 512 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (512 + 15 * 4) =
      expectedWord (512 + 15 * 4) from
        read_patterned 512 15 (by omega) (by omega)]
  decide

theorem schedule9 : CompressionCorrect.schedule patternedInput 576 = block9 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (576 + 0 * 4) =
      expectedWord (576 + 0 * 4) from
        read_patterned 576 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 1 * 4) =
      expectedWord (576 + 1 * 4) from
        read_patterned 576 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 2 * 4) =
      expectedWord (576 + 2 * 4) from
        read_patterned 576 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 3 * 4) =
      expectedWord (576 + 3 * 4) from
        read_patterned 576 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 4 * 4) =
      expectedWord (576 + 4 * 4) from
        read_patterned 576 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 5 * 4) =
      expectedWord (576 + 5 * 4) from
        read_patterned 576 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 6 * 4) =
      expectedWord (576 + 6 * 4) from
        read_patterned 576 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 7 * 4) =
      expectedWord (576 + 7 * 4) from
        read_patterned 576 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 8 * 4) =
      expectedWord (576 + 8 * 4) from
        read_patterned 576 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 9 * 4) =
      expectedWord (576 + 9 * 4) from
        read_patterned 576 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 10 * 4) =
      expectedWord (576 + 10 * 4) from
        read_patterned 576 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 11 * 4) =
      expectedWord (576 + 11 * 4) from
        read_patterned 576 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 12 * 4) =
      expectedWord (576 + 12 * 4) from
        read_patterned 576 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 13 * 4) =
      expectedWord (576 + 13 * 4) from
        read_patterned 576 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 14 * 4) =
      expectedWord (576 + 14 * 4) from
        read_patterned 576 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (576 + 15 * 4) =
      expectedWord (576 + 15 * 4) from
        read_patterned 576 15 (by omega) (by omega)]
  decide


end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
