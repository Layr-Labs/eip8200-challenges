import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_768_0 :
    Ripemd160.readLE32 patternedInput 768 = 0x97724d28 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 768 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 768 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 768 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 768 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_1 :
    Ripemd160.readLE32 patternedInput 772 = 0x2b06e1bc := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 772 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 772 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 772 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 772 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_2 :
    Ripemd160.readLE32 patternedInput 776 = 0xbf9a7550 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 776 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 776 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 776 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 776 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_3 :
    Ripemd160.readLE32 patternedInput 780 = 0x532e09e4 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 780 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 780 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 780 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 780 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_4 :
    Ripemd160.readLE32 patternedInput 784 = 0xe7c29d78 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 784 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 784 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 784 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 784 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_5 :
    Ripemd160.readLE32 patternedInput 788 = 0x7b56310c := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 788 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 788 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 788 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 788 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_6 :
    Ripemd160.readLE32 patternedInput 792 = 0x0feac5a0 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 792 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 792 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 792 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 792 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_7 :
    Ripemd160.readLE32 patternedInput 796 = 0xa37e5934 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 796 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 796 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 796 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 796 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_8 :
    Ripemd160.readLE32 patternedInput 800 = 0x3712edc8 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 800 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 800 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 800 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 800 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_9 :
    Ripemd160.readLE32 patternedInput 804 = 0xcba6815c := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 804 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 804 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 804 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 804 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_10 :
    Ripemd160.readLE32 patternedInput 808 = 0x5f3a15f0 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 808 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 808 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 808 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 808 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_11 :
    Ripemd160.readLE32 patternedInput 812 = 0xf3cea984 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 812 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 812 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 812 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 812 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_12 :
    Ripemd160.readLE32 patternedInput 816 = 0x87623d18 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 816 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 816 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 816 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 816 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_13 :
    Ripemd160.readLE32 patternedInput 820 = 0x1bf6d1ac := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 820 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 820 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 820 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 820 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_14 :
    Ripemd160.readLE32 patternedInput 824 = 0xaf8a6540 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 824 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 824 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 824 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 824 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_768_15 :
    Ripemd160.readLE32 patternedInput 828 = 0x431ef9d4 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 828 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 828 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 828 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 828 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem schedule12 : CompressionCorrect.schedule patternedInput 768 = block12 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_768_0]
  rw [read_768_1]
  rw [read_768_2]
  rw [read_768_3]
  rw [read_768_4]
  rw [read_768_5]
  rw [read_768_6]
  rw [read_768_7]
  rw [read_768_8]
  rw [read_768_9]
  rw [read_768_10]
  rw [read_768_11]
  rw [read_768_12]
  rw [read_768_13]
  rw [read_768_14]
  rw [read_768_15]
  decide

theorem compress12 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 768 =
      CompressionCorrect.normalizedCompress h block12 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule12]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
