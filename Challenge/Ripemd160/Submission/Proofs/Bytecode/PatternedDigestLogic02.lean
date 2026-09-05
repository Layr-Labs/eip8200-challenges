import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_128_0 :
    Ripemd160.readLE32 patternedInput 128 = 0xf6d1ac87 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 128 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 128 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 128 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 128 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_1 :
    Ripemd160.readLE32 patternedInput 132 = 0x8a65401b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 132 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 132 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 132 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 132 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_2 :
    Ripemd160.readLE32 patternedInput 136 = 0x1ef9d4af := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 136 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 136 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 136 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 136 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_3 :
    Ripemd160.readLE32 patternedInput 140 = 0xb28d6843 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 140 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 140 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 140 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 140 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_4 :
    Ripemd160.readLE32 patternedInput 144 = 0x4621fcd7 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 144 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 144 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 144 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 144 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_5 :
    Ripemd160.readLE32 patternedInput 148 = 0xdab5906b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 148 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 148 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 148 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 148 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_6 :
    Ripemd160.readLE32 patternedInput 152 = 0x6e4924ff := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 152 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 152 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 152 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 152 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_7 :
    Ripemd160.readLE32 patternedInput 156 = 0x02ddb893 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 156 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 156 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 156 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 156 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_8 :
    Ripemd160.readLE32 patternedInput 160 = 0x96714c27 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 160 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 160 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 160 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 160 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_9 :
    Ripemd160.readLE32 patternedInput 164 = 0x2a05e0bb := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 164 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 164 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 164 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 164 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_10 :
    Ripemd160.readLE32 patternedInput 168 = 0xbe99744f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 168 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 168 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 168 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 168 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_11 :
    Ripemd160.readLE32 patternedInput 172 = 0x522d08e3 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 172 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 172 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 172 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 172 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_12 :
    Ripemd160.readLE32 patternedInput 176 = 0xe6c19c77 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 176 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 176 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 176 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 176 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_13 :
    Ripemd160.readLE32 patternedInput 180 = 0x7a55300b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 180 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 180 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 180 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 180 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_14 :
    Ripemd160.readLE32 patternedInput 184 = 0x0ee9c49f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 184 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 184 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 184 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 184 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_128_15 :
    Ripemd160.readLE32 patternedInput 188 = 0xa27d5833 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 188 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 188 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 188 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 188 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem schedule2 : CompressionCorrect.schedule patternedInput 128 = block2 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_128_0]
  rw [read_128_1]
  rw [read_128_2]
  rw [read_128_3]
  rw [read_128_4]
  rw [read_128_5]
  rw [read_128_6]
  rw [read_128_7]
  rw [read_128_8]
  rw [read_128_9]
  rw [read_128_10]
  rw [read_128_11]
  rw [read_128_12]
  rw [read_128_13]
  rw [read_128_14]
  rw [read_128_15]
  decide

theorem compress2 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 128 =
      CompressionCorrect.normalizedCompress h block2 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule2]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
