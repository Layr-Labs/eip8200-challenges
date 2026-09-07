import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSchedulesB

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem schedule10 : CompressionCorrect.schedule patternedInput 640 = block10 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (640 + 0 * 4) =
      expectedWord (640 + 0 * 4) from
        read_patterned 640 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 1 * 4) =
      expectedWord (640 + 1 * 4) from
        read_patterned 640 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 2 * 4) =
      expectedWord (640 + 2 * 4) from
        read_patterned 640 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 3 * 4) =
      expectedWord (640 + 3 * 4) from
        read_patterned 640 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 4 * 4) =
      expectedWord (640 + 4 * 4) from
        read_patterned 640 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 5 * 4) =
      expectedWord (640 + 5 * 4) from
        read_patterned 640 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 6 * 4) =
      expectedWord (640 + 6 * 4) from
        read_patterned 640 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 7 * 4) =
      expectedWord (640 + 7 * 4) from
        read_patterned 640 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 8 * 4) =
      expectedWord (640 + 8 * 4) from
        read_patterned 640 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 9 * 4) =
      expectedWord (640 + 9 * 4) from
        read_patterned 640 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 10 * 4) =
      expectedWord (640 + 10 * 4) from
        read_patterned 640 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 11 * 4) =
      expectedWord (640 + 11 * 4) from
        read_patterned 640 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 12 * 4) =
      expectedWord (640 + 12 * 4) from
        read_patterned 640 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 13 * 4) =
      expectedWord (640 + 13 * 4) from
        read_patterned 640 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 14 * 4) =
      expectedWord (640 + 14 * 4) from
        read_patterned 640 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (640 + 15 * 4) =
      expectedWord (640 + 15 * 4) from
        read_patterned 640 15 (by omega) (by omega)]
  decide

theorem schedule11 : CompressionCorrect.schedule patternedInput 704 = block11 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (704 + 0 * 4) =
      expectedWord (704 + 0 * 4) from
        read_patterned 704 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 1 * 4) =
      expectedWord (704 + 1 * 4) from
        read_patterned 704 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 2 * 4) =
      expectedWord (704 + 2 * 4) from
        read_patterned 704 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 3 * 4) =
      expectedWord (704 + 3 * 4) from
        read_patterned 704 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 4 * 4) =
      expectedWord (704 + 4 * 4) from
        read_patterned 704 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 5 * 4) =
      expectedWord (704 + 5 * 4) from
        read_patterned 704 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 6 * 4) =
      expectedWord (704 + 6 * 4) from
        read_patterned 704 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 7 * 4) =
      expectedWord (704 + 7 * 4) from
        read_patterned 704 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 8 * 4) =
      expectedWord (704 + 8 * 4) from
        read_patterned 704 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 9 * 4) =
      expectedWord (704 + 9 * 4) from
        read_patterned 704 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 10 * 4) =
      expectedWord (704 + 10 * 4) from
        read_patterned 704 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 11 * 4) =
      expectedWord (704 + 11 * 4) from
        read_patterned 704 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 12 * 4) =
      expectedWord (704 + 12 * 4) from
        read_patterned 704 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 13 * 4) =
      expectedWord (704 + 13 * 4) from
        read_patterned 704 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 14 * 4) =
      expectedWord (704 + 14 * 4) from
        read_patterned 704 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (704 + 15 * 4) =
      expectedWord (704 + 15 * 4) from
        read_patterned 704 15 (by omega) (by omega)]
  decide

theorem schedule12 : CompressionCorrect.schedule patternedInput 768 = block12 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (768 + 0 * 4) =
      expectedWord (768 + 0 * 4) from
        read_patterned 768 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 1 * 4) =
      expectedWord (768 + 1 * 4) from
        read_patterned 768 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 2 * 4) =
      expectedWord (768 + 2 * 4) from
        read_patterned 768 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 3 * 4) =
      expectedWord (768 + 3 * 4) from
        read_patterned 768 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 4 * 4) =
      expectedWord (768 + 4 * 4) from
        read_patterned 768 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 5 * 4) =
      expectedWord (768 + 5 * 4) from
        read_patterned 768 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 6 * 4) =
      expectedWord (768 + 6 * 4) from
        read_patterned 768 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 7 * 4) =
      expectedWord (768 + 7 * 4) from
        read_patterned 768 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 8 * 4) =
      expectedWord (768 + 8 * 4) from
        read_patterned 768 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 9 * 4) =
      expectedWord (768 + 9 * 4) from
        read_patterned 768 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 10 * 4) =
      expectedWord (768 + 10 * 4) from
        read_patterned 768 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 11 * 4) =
      expectedWord (768 + 11 * 4) from
        read_patterned 768 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 12 * 4) =
      expectedWord (768 + 12 * 4) from
        read_patterned 768 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 13 * 4) =
      expectedWord (768 + 13 * 4) from
        read_patterned 768 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 14 * 4) =
      expectedWord (768 + 14 * 4) from
        read_patterned 768 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (768 + 15 * 4) =
      expectedWord (768 + 15 * 4) from
        read_patterned 768 15 (by omega) (by omega)]
  decide

theorem schedule13 : CompressionCorrect.schedule patternedInput 832 = block13 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (832 + 0 * 4) =
      expectedWord (832 + 0 * 4) from
        read_patterned 832 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 1 * 4) =
      expectedWord (832 + 1 * 4) from
        read_patterned 832 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 2 * 4) =
      expectedWord (832 + 2 * 4) from
        read_patterned 832 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 3 * 4) =
      expectedWord (832 + 3 * 4) from
        read_patterned 832 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 4 * 4) =
      expectedWord (832 + 4 * 4) from
        read_patterned 832 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 5 * 4) =
      expectedWord (832 + 5 * 4) from
        read_patterned 832 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 6 * 4) =
      expectedWord (832 + 6 * 4) from
        read_patterned 832 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 7 * 4) =
      expectedWord (832 + 7 * 4) from
        read_patterned 832 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 8 * 4) =
      expectedWord (832 + 8 * 4) from
        read_patterned 832 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 9 * 4) =
      expectedWord (832 + 9 * 4) from
        read_patterned 832 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 10 * 4) =
      expectedWord (832 + 10 * 4) from
        read_patterned 832 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 11 * 4) =
      expectedWord (832 + 11 * 4) from
        read_patterned 832 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 12 * 4) =
      expectedWord (832 + 12 * 4) from
        read_patterned 832 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 13 * 4) =
      expectedWord (832 + 13 * 4) from
        read_patterned 832 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 14 * 4) =
      expectedWord (832 + 14 * 4) from
        read_patterned 832 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (832 + 15 * 4) =
      expectedWord (832 + 15 * 4) from
        read_patterned 832 15 (by omega) (by omega)]
  decide

theorem schedule14 : CompressionCorrect.schedule patternedInput 896 = block14 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 patternedInput (896 + 0 * 4) =
      expectedWord (896 + 0 * 4) from
        read_patterned 896 0 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 1 * 4) =
      expectedWord (896 + 1 * 4) from
        read_patterned 896 1 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 2 * 4) =
      expectedWord (896 + 2 * 4) from
        read_patterned 896 2 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 3 * 4) =
      expectedWord (896 + 3 * 4) from
        read_patterned 896 3 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 4 * 4) =
      expectedWord (896 + 4 * 4) from
        read_patterned 896 4 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 5 * 4) =
      expectedWord (896 + 5 * 4) from
        read_patterned 896 5 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 6 * 4) =
      expectedWord (896 + 6 * 4) from
        read_patterned 896 6 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 7 * 4) =
      expectedWord (896 + 7 * 4) from
        read_patterned 896 7 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 8 * 4) =
      expectedWord (896 + 8 * 4) from
        read_patterned 896 8 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 9 * 4) =
      expectedWord (896 + 9 * 4) from
        read_patterned 896 9 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 10 * 4) =
      expectedWord (896 + 10 * 4) from
        read_patterned 896 10 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 11 * 4) =
      expectedWord (896 + 11 * 4) from
        read_patterned 896 11 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 12 * 4) =
      expectedWord (896 + 12 * 4) from
        read_patterned 896 12 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 13 * 4) =
      expectedWord (896 + 13 * 4) from
        read_patterned 896 13 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 14 * 4) =
      expectedWord (896 + 14 * 4) from
        read_patterned 896 14 (by omega) (by omega)]
  rw [show Ripemd160.readLE32 patternedInput (896 + 15 * 4) =
      expectedWord (896 + 15 * 4) from
        read_patterned 896 15 (by omega) (by omega)]
  decide


end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
