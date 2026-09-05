import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_0_0 :
    Ripemd160.readLE32 patternedInput 0 = 0x76512c07 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 0 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 0 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 0 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 0 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_1 :
    Ripemd160.readLE32 patternedInput 4 = 0x0ae5c09b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 4 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 4 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 4 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 4 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_2 :
    Ripemd160.readLE32 patternedInput 8 = 0x9e79542f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 8 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 8 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 8 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 8 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_3 :
    Ripemd160.readLE32 patternedInput 12 = 0x320de8c3 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 12 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 12 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 12 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 12 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_4 :
    Ripemd160.readLE32 patternedInput 16 = 0xc6a17c57 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 16 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 16 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 16 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 16 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_5 :
    Ripemd160.readLE32 patternedInput 20 = 0x5a3510eb := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 20 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 20 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 20 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 20 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_6 :
    Ripemd160.readLE32 patternedInput 24 = 0xeec9a47f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 24 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 24 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 24 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 24 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_7 :
    Ripemd160.readLE32 patternedInput 28 = 0x825d3813 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 28 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 28 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 28 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 28 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_8 :
    Ripemd160.readLE32 patternedInput 32 = 0x16f1cca7 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 32 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 32 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 32 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 32 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_9 :
    Ripemd160.readLE32 patternedInput 36 = 0xaa85603b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 36 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 36 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 36 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 36 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_10 :
    Ripemd160.readLE32 patternedInput 40 = 0x3e19f4cf := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 40 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 40 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 40 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 40 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_11 :
    Ripemd160.readLE32 patternedInput 44 = 0xd2ad8863 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 44 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 44 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 44 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 44 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_12 :
    Ripemd160.readLE32 patternedInput 48 = 0x66411cf7 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 48 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 48 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 48 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 48 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_13 :
    Ripemd160.readLE32 patternedInput 52 = 0xfad5b08b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 52 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 52 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 52 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 52 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_14 :
    Ripemd160.readLE32 patternedInput 56 = 0x8e69441f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 56 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 56 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 56 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 56 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_15 :
    Ripemd160.readLE32 patternedInput 60 = 0x22fdd8b3 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 60 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 60 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 60 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 60 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem schedule0 : CompressionCorrect.schedule patternedInput 0 = block0 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_0_0]
  rw [read_0_1]
  rw [read_0_2]
  rw [read_0_3]
  rw [read_0_4]
  rw [read_0_5]
  rw [read_0_6]
  rw [read_0_7]
  rw [read_0_8]
  rw [read_0_9]
  rw [read_0_10]
  rw [read_0_11]
  rw [read_0_12]
  rw [read_0_13]
  rw [read_0_14]
  rw [read_0_15]
  decide

theorem compress0 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 0 =
      CompressionCorrect.normalizedCompress h block0 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule0]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
