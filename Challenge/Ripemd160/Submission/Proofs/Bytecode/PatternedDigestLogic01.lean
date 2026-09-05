import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_64_0 :
    Ripemd160.readLE32 patternedInput 64 = 0xb6916c47 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 64 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 64 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 64 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 64 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_1 :
    Ripemd160.readLE32 patternedInput 68 = 0x4a2500db := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 68 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 68 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 68 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 68 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_2 :
    Ripemd160.readLE32 patternedInput 72 = 0xdeb9946f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 72 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 72 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 72 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 72 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_3 :
    Ripemd160.readLE32 patternedInput 76 = 0x724d2803 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 76 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 76 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 76 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 76 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_4 :
    Ripemd160.readLE32 patternedInput 80 = 0x06e1bc97 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 80 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 80 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 80 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 80 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_5 :
    Ripemd160.readLE32 patternedInput 84 = 0x9a75502b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 84 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 84 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 84 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 84 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_6 :
    Ripemd160.readLE32 patternedInput 88 = 0x2e09e4bf := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 88 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 88 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 88 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 88 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_7 :
    Ripemd160.readLE32 patternedInput 92 = 0xc29d7853 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 92 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 92 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 92 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 92 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_8 :
    Ripemd160.readLE32 patternedInput 96 = 0x56310ce7 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 96 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 96 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 96 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 96 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_9 :
    Ripemd160.readLE32 patternedInput 100 = 0xeac5a07b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 100 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 100 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 100 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 100 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_10 :
    Ripemd160.readLE32 patternedInput 104 = 0x7e59340f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 104 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 104 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 104 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 104 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_11 :
    Ripemd160.readLE32 patternedInput 108 = 0x12edc8a3 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 108 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 108 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 108 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 108 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_12 :
    Ripemd160.readLE32 patternedInput 112 = 0xa6815c37 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 112 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 112 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 112 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 112 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_13 :
    Ripemd160.readLE32 patternedInput 116 = 0x3a15f0cb := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 116 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 116 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 116 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 116 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_14 :
    Ripemd160.readLE32 patternedInput 120 = 0xcea9845f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 120 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 120 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 120 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 120 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_64_15 :
    Ripemd160.readLE32 patternedInput 124 = 0x623d18f3 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 124 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 124 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 124 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 124 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem schedule1 : CompressionCorrect.schedule patternedInput 64 = block1 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_64_0]
  rw [read_64_1]
  rw [read_64_2]
  rw [read_64_3]
  rw [read_64_4]
  rw [read_64_5]
  rw [read_64_6]
  rw [read_64_7]
  rw [read_64_8]
  rw [read_64_9]
  rw [read_64_10]
  rw [read_64_11]
  rw [read_64_12]
  rw [read_64_13]
  rw [read_64_14]
  rw [read_64_15]
  decide

theorem compress1 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 64 =
      CompressionCorrect.normalizedCompress h block1 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule1]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
