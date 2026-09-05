import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_256_0 :
    Ripemd160.readLE32 patternedInput 256 = 0x815c3712 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 256 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 256 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 256 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 256 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_1 :
    Ripemd160.readLE32 patternedInput 260 = 0x15f0cba6 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 260 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 260 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 260 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 260 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_2 :
    Ripemd160.readLE32 patternedInput 264 = 0xa9845f3a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 264 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 264 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 264 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 264 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_3 :
    Ripemd160.readLE32 patternedInput 268 = 0x3d18f3ce := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 268 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 268 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 268 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 268 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_4 :
    Ripemd160.readLE32 patternedInput 272 = 0xd1ac8762 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 272 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 272 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 272 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 272 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_5 :
    Ripemd160.readLE32 patternedInput 276 = 0x65401bf6 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 276 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 276 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 276 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 276 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_6 :
    Ripemd160.readLE32 patternedInput 280 = 0xf9d4af8a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 280 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 280 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 280 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 280 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_7 :
    Ripemd160.readLE32 patternedInput 284 = 0x8d68431e := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 284 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 284 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 284 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 284 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_8 :
    Ripemd160.readLE32 patternedInput 288 = 0x21fcd7b2 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 288 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 288 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 288 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 288 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_9 :
    Ripemd160.readLE32 patternedInput 292 = 0xb5906b46 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 292 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 292 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 292 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 292 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_10 :
    Ripemd160.readLE32 patternedInput 296 = 0x4924ffda := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 296 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 296 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 296 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 296 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_11 :
    Ripemd160.readLE32 patternedInput 300 = 0xddb8936e := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 300 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 300 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 300 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 300 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_12 :
    Ripemd160.readLE32 patternedInput 304 = 0x714c2702 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 304 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 304 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 304 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 304 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_13 :
    Ripemd160.readLE32 patternedInput 308 = 0x05e0bb96 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 308 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 308 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 308 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 308 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_14 :
    Ripemd160.readLE32 patternedInput 312 = 0x99744f2a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 312 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 312 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 312 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 312 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_256_15 :
    Ripemd160.readLE32 patternedInput 316 = 0x2d08e3be := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 316 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 316 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 316 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 316 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem schedule4 : CompressionCorrect.schedule patternedInput 256 = block4 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_256_0]
  rw [read_256_1]
  rw [read_256_2]
  rw [read_256_3]
  rw [read_256_4]
  rw [read_256_5]
  rw [read_256_6]
  rw [read_256_7]
  rw [read_256_8]
  rw [read_256_9]
  rw [read_256_10]
  rw [read_256_11]
  rw [read_256_12]
  rw [read_256_13]
  rw [read_256_14]
  rw [read_256_15]
  decide

theorem compress4 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 256 =
      CompressionCorrect.normalizedCompress h block4 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule4]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
