import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_896_0 :
    Ripemd160.readLE32 patternedInput 896 = 0x17f2cda8 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 896 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 896 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 896 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 896 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_1 :
    Ripemd160.readLE32 patternedInput 900 = 0xab86613c := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 900 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 900 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 900 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 900 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_2 :
    Ripemd160.readLE32 patternedInput 904 = 0x3f1af5d0 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 904 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 904 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 904 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 904 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_3 :
    Ripemd160.readLE32 patternedInput 908 = 0xd3ae8964 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 908 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 908 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 908 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 908 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_4 :
    Ripemd160.readLE32 patternedInput 912 = 0x67421df8 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 912 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 912 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 912 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 912 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_5 :
    Ripemd160.readLE32 patternedInput 916 = 0xfbd6b18c := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 916 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 916 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 916 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 916 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_6 :
    Ripemd160.readLE32 patternedInput 920 = 0x8f6a4520 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 920 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 920 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 920 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 920 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_7 :
    Ripemd160.readLE32 patternedInput 924 = 0x23fed9b4 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 924 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 924 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 924 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 924 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_8 :
    Ripemd160.readLE32 patternedInput 928 = 0xb7926d48 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 928 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 928 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 928 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 928 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_9 :
    Ripemd160.readLE32 patternedInput 932 = 0x4b2601dc := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 932 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 932 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 932 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 932 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_10 :
    Ripemd160.readLE32 patternedInput 936 = 0xdfba9570 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 936 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 936 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 936 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 936 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_11 :
    Ripemd160.readLE32 patternedInput 940 = 0x734e2904 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 940 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 940 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 940 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 940 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_12 :
    Ripemd160.readLE32 patternedInput 944 = 0x07e2bd98 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 944 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 944 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 944 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 944 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_13 :
    Ripemd160.readLE32 patternedInput 948 = 0x9b76512c := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 948 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 948 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 948 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 948 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_14 :
    Ripemd160.readLE32 patternedInput 952 = 0x2f0ae5c0 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 952 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 952 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 952 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 952 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_896_15 :
    Ripemd160.readLE32 patternedInput 956 = 0xc39e7954 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 956 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 956 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 956 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 956 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem schedule14 : CompressionCorrect.schedule patternedInput 896 = block14 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_896_0]
  rw [read_896_1]
  rw [read_896_2]
  rw [read_896_3]
  rw [read_896_4]
  rw [read_896_5]
  rw [read_896_6]
  rw [read_896_7]
  rw [read_896_8]
  rw [read_896_9]
  rw [read_896_10]
  rw [read_896_11]
  rw [read_896_12]
  rw [read_896_13]
  rw [read_896_14]
  rw [read_896_15]
  decide

theorem compress14 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 896 =
      CompressionCorrect.normalizedCompress h block14 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule14]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
