import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_576_0 :
    Ripemd160.readLE32 patternedInput 576 = 0xcca7825d := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 576 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 576 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 576 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 576 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_1 :
    Ripemd160.readLE32 patternedInput 580 = 0x603b16f1 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 580 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 580 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 580 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 580 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_2 :
    Ripemd160.readLE32 patternedInput 584 = 0xf4cfaa85 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 584 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 584 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 584 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 584 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_3 :
    Ripemd160.readLE32 patternedInput 588 = 0x88633e19 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 588 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 588 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 588 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 588 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_4 :
    Ripemd160.readLE32 patternedInput 592 = 0x1cf7d2ad := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 592 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 592 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 592 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 592 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_5 :
    Ripemd160.readLE32 patternedInput 596 = 0xb08b6641 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 596 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 596 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 596 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 596 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_6 :
    Ripemd160.readLE32 patternedInput 600 = 0x441ffad5 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 600 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 600 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 600 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 600 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_7 :
    Ripemd160.readLE32 patternedInput 604 = 0xd8b38e69 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 604 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 604 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 604 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 604 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_8 :
    Ripemd160.readLE32 patternedInput 608 = 0x6c4722fd := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 608 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 608 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 608 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 608 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_9 :
    Ripemd160.readLE32 patternedInput 612 = 0x00dbb691 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 612 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 612 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 612 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 612 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_10 :
    Ripemd160.readLE32 patternedInput 616 = 0x946f4a25 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 616 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 616 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 616 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 616 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_11 :
    Ripemd160.readLE32 patternedInput 620 = 0x2803deb9 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 620 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 620 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 620 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 620 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_12 :
    Ripemd160.readLE32 patternedInput 624 = 0xbc97724d := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 624 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 624 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 624 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 624 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_13 :
    Ripemd160.readLE32 patternedInput 628 = 0x502b06e1 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 628 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 628 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 628 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 628 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_14 :
    Ripemd160.readLE32 patternedInput 632 = 0xe4bf9a75 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 632 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 632 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 632 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 632 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_576_15 :
    Ripemd160.readLE32 patternedInput 636 = 0x78532e09 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 636 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 636 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 636 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 636 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem schedule9 : CompressionCorrect.schedule patternedInput 576 = block9 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_576_0]
  rw [read_576_1]
  rw [read_576_2]
  rw [read_576_3]
  rw [read_576_4]
  rw [read_576_5]
  rw [read_576_6]
  rw [read_576_7]
  rw [read_576_8]
  rw [read_576_9]
  rw [read_576_10]
  rw [read_576_11]
  rw [read_576_12]
  rw [read_576_13]
  rw [read_576_14]
  rw [read_576_15]
  decide

theorem compress9 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 576 =
      CompressionCorrect.normalizedCompress h block9 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule9]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
