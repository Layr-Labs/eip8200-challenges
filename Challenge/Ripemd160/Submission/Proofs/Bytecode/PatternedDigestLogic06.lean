import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_384_0 :
    Ripemd160.readLE32 patternedInput 384 = 0x01dcb792 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 384 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 384 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 384 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 384 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_1 :
    Ripemd160.readLE32 patternedInput 388 = 0x95704b26 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 388 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 388 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 388 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 388 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_2 :
    Ripemd160.readLE32 patternedInput 392 = 0x2904dfba := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 392 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 392 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 392 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 392 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_3 :
    Ripemd160.readLE32 patternedInput 396 = 0xbd98734e := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 396 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 396 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 396 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 396 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_4 :
    Ripemd160.readLE32 patternedInput 400 = 0x512c07e2 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 400 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 400 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 400 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 400 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_5 :
    Ripemd160.readLE32 patternedInput 404 = 0xe5c09b76 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 404 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 404 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 404 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 404 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_6 :
    Ripemd160.readLE32 patternedInput 408 = 0x79542f0a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 408 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 408 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 408 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 408 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_7 :
    Ripemd160.readLE32 patternedInput 412 = 0x0de8c39e := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 412 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 412 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 412 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 412 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_8 :
    Ripemd160.readLE32 patternedInput 416 = 0xa17c5732 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 416 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 416 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 416 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 416 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_9 :
    Ripemd160.readLE32 patternedInput 420 = 0x3510ebc6 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 420 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 420 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 420 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 420 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_10 :
    Ripemd160.readLE32 patternedInput 424 = 0xc9a47f5a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 424 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 424 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 424 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 424 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_11 :
    Ripemd160.readLE32 patternedInput 428 = 0x5d3813ee := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 428 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 428 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 428 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 428 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_12 :
    Ripemd160.readLE32 patternedInput 432 = 0xf1cca782 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 432 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 432 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 432 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 432 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_13 :
    Ripemd160.readLE32 patternedInput 436 = 0x85603b16 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 436 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 436 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 436 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 436 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_14 :
    Ripemd160.readLE32 patternedInput 440 = 0x19f4cfaa := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 440 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 440 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 440 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 440 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_384_15 :
    Ripemd160.readLE32 patternedInput 444 = 0xad88633e := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 444 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 444 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 444 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 444 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem schedule6 : CompressionCorrect.schedule patternedInput 384 = block6 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_384_0]
  rw [read_384_1]
  rw [read_384_2]
  rw [read_384_3]
  rw [read_384_4]
  rw [read_384_5]
  rw [read_384_6]
  rw [read_384_7]
  rw [read_384_8]
  rw [read_384_9]
  rw [read_384_10]
  rw [read_384_11]
  rw [read_384_12]
  rw [read_384_13]
  rw [read_384_14]
  rw [read_384_15]
  decide

theorem compress6 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 384 =
      CompressionCorrect.normalizedCompress h block6 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule6]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
