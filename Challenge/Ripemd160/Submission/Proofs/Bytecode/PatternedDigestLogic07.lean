import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_448_0 :
    Ripemd160.readLE32 patternedInput 448 = 0x411cf7d2 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 448 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 448 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 448 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 448 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_1 :
    Ripemd160.readLE32 patternedInput 452 = 0xd5b08b66 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 452 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 452 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 452 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 452 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_2 :
    Ripemd160.readLE32 patternedInput 456 = 0x69441ffa := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 456 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 456 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 456 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 456 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_3 :
    Ripemd160.readLE32 patternedInput 460 = 0xfdd8b38e := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 460 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 460 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 460 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 460 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_4 :
    Ripemd160.readLE32 patternedInput 464 = 0x916c4722 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 464 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 464 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 464 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 464 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_5 :
    Ripemd160.readLE32 patternedInput 468 = 0x2500dbb6 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 468 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 468 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 468 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 468 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_6 :
    Ripemd160.readLE32 patternedInput 472 = 0xb9946f4a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 472 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 472 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 472 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 472 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_7 :
    Ripemd160.readLE32 patternedInput 476 = 0x4d2803de := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 476 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 476 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 476 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 476 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_8 :
    Ripemd160.readLE32 patternedInput 480 = 0xe1bc9772 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 480 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 480 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 480 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 480 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_9 :
    Ripemd160.readLE32 patternedInput 484 = 0x75502b06 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 484 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 484 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 484 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 484 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_10 :
    Ripemd160.readLE32 patternedInput 488 = 0x09e4bf9a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 488 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 488 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 488 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 488 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_11 :
    Ripemd160.readLE32 patternedInput 492 = 0x9d78532e := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 492 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 492 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 492 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 492 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_12 :
    Ripemd160.readLE32 patternedInput 496 = 0x310ce7c2 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 496 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 496 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 496 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 496 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_13 :
    Ripemd160.readLE32 patternedInput 500 = 0xd0ab7b56 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 500 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 500 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 500 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 500 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_14 :
    Ripemd160.readLE32 patternedInput 504 = 0x643f1af5 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 504 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 504 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 504 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 504 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_448_15 :
    Ripemd160.readLE32 patternedInput 508 = 0xf8d3ae89 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 508 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 508 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 508 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 508 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem schedule7 : CompressionCorrect.schedule patternedInput 448 = block7 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_448_0]
  rw [read_448_1]
  rw [read_448_2]
  rw [read_448_3]
  rw [read_448_4]
  rw [read_448_5]
  rw [read_448_6]
  rw [read_448_7]
  rw [read_448_8]
  rw [read_448_9]
  rw [read_448_10]
  rw [read_448_11]
  rw [read_448_12]
  rw [read_448_13]
  rw [read_448_14]
  rw [read_448_15]
  decide

theorem compress7 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 448 =
      CompressionCorrect.normalizedCompress h block7 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule7]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
