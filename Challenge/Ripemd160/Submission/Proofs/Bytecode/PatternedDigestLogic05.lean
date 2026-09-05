import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_320_0 :
    Ripemd160.readLE32 patternedInput 320 = 0xc19c7752 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 320 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 320 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 320 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 320 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_1 :
    Ripemd160.readLE32 patternedInput 324 = 0x55300be6 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 324 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 324 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 324 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 324 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_2 :
    Ripemd160.readLE32 patternedInput 328 = 0xe9c49f7a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 328 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 328 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 328 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 328 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_3 :
    Ripemd160.readLE32 patternedInput 332 = 0x7d58330e := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 332 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 332 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 332 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 332 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_4 :
    Ripemd160.readLE32 patternedInput 336 = 0x11ecc7a2 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 336 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 336 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 336 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 336 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_5 :
    Ripemd160.readLE32 patternedInput 340 = 0xa5805b36 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 340 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 340 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 340 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 340 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_6 :
    Ripemd160.readLE32 patternedInput 344 = 0x3914efca := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 344 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 344 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 344 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 344 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_7 :
    Ripemd160.readLE32 patternedInput 348 = 0xcda8835e := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 348 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 348 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 348 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 348 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_8 :
    Ripemd160.readLE32 patternedInput 352 = 0x613c17f2 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 352 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 352 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 352 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 352 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_9 :
    Ripemd160.readLE32 patternedInput 356 = 0xf5d0ab86 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 356 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 356 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 356 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 356 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_10 :
    Ripemd160.readLE32 patternedInput 360 = 0x89643f1a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 360 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 360 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 360 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 360 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_11 :
    Ripemd160.readLE32 patternedInput 364 = 0x1df8d3ae := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 364 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 364 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 364 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 364 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_12 :
    Ripemd160.readLE32 patternedInput 368 = 0xb18c6742 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 368 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 368 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 368 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 368 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_13 :
    Ripemd160.readLE32 patternedInput 372 = 0x4520fbd6 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 372 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 372 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 372 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 372 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_14 :
    Ripemd160.readLE32 patternedInput 376 = 0xd9b48f6a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 376 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 376 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 376 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 376 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_15 :
    Ripemd160.readLE32 patternedInput 380 = 0x6d4823fe := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 380 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 380 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 380 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 380 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem schedule5 : CompressionCorrect.schedule patternedInput 320 = block5 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_320_0]
  rw [read_320_1]
  rw [read_320_2]
  rw [read_320_3]
  rw [read_320_4]
  rw [read_320_5]
  rw [read_320_6]
  rw [read_320_7]
  rw [read_320_8]
  rw [read_320_9]
  rw [read_320_10]
  rw [read_320_11]
  rw [read_320_12]
  rw [read_320_13]
  rw [read_320_14]
  rw [read_320_15]
  decide

theorem compress5 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 320 =
      CompressionCorrect.normalizedCompress h block5 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule5]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
