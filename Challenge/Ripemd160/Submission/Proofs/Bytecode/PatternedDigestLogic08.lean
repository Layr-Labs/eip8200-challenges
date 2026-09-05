import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_512_0 :
    Ripemd160.readLE32 patternedInput 512 = 0x8c67421d := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 512 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 512 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 512 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 512 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_1 :
    Ripemd160.readLE32 patternedInput 516 = 0x20fbd6b1 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 516 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 516 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 516 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 516 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_2 :
    Ripemd160.readLE32 patternedInput 520 = 0xb48f6a45 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 520 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 520 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 520 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 520 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_3 :
    Ripemd160.readLE32 patternedInput 524 = 0x4823fed9 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 524 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 524 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 524 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 524 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_4 :
    Ripemd160.readLE32 patternedInput 528 = 0xdcb7926d := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 528 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 528 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 528 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 528 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_5 :
    Ripemd160.readLE32 patternedInput 532 = 0x704b2601 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 532 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 532 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 532 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 532 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_6 :
    Ripemd160.readLE32 patternedInput 536 = 0x04dfba95 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 536 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 536 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 536 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 536 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_7 :
    Ripemd160.readLE32 patternedInput 540 = 0x98734e29 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 540 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 540 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 540 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 540 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_8 :
    Ripemd160.readLE32 patternedInput 544 = 0x2c07e2bd := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 544 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 544 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 544 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 544 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_9 :
    Ripemd160.readLE32 patternedInput 548 = 0xc09b7651 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 548 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 548 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 548 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 548 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_10 :
    Ripemd160.readLE32 patternedInput 552 = 0x542f0ae5 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 552 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 552 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 552 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 552 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_11 :
    Ripemd160.readLE32 patternedInput 556 = 0xe8c39e79 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 556 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 556 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 556 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 556 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_12 :
    Ripemd160.readLE32 patternedInput 560 = 0x7c57320d := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 560 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 560 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 560 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 560 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_13 :
    Ripemd160.readLE32 patternedInput 564 = 0x10ebc6a1 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 564 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 564 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 564 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 564 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_14 :
    Ripemd160.readLE32 patternedInput 568 = 0xa47f5a35 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 568 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 568 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 568 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 568 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_512_15 :
    Ripemd160.readLE32 patternedInput 572 = 0x3813eec9 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 572 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 572 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 572 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 572 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem schedule8 : CompressionCorrect.schedule patternedInput 512 = block8 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_512_0]
  rw [read_512_1]
  rw [read_512_2]
  rw [read_512_3]
  rw [read_512_4]
  rw [read_512_5]
  rw [read_512_6]
  rw [read_512_7]
  rw [read_512_8]
  rw [read_512_9]
  rw [read_512_10]
  rw [read_512_11]
  rw [read_512_12]
  rw [read_512_13]
  rw [read_512_14]
  rw [read_512_15]
  decide

theorem compress8 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 512 =
      CompressionCorrect.normalizedCompress h block8 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule8]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
