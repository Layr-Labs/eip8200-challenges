import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_192_0 :
    Ripemd160.readLE32 patternedInput 192 = 0x3611ecc7 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 192 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 192 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 192 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 192 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_1 :
    Ripemd160.readLE32 patternedInput 196 = 0xcaa5805b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 196 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 196 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 196 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 196 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_2 :
    Ripemd160.readLE32 patternedInput 200 = 0x5e3914ef := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 200 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 200 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 200 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 200 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_3 :
    Ripemd160.readLE32 patternedInput 204 = 0xf2cda883 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 204 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 204 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 204 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 204 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_4 :
    Ripemd160.readLE32 patternedInput 208 = 0x86613c17 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 208 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 208 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 208 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 208 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_5 :
    Ripemd160.readLE32 patternedInput 212 = 0x1af5d0ab := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 212 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 212 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 212 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 212 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_6 :
    Ripemd160.readLE32 patternedInput 216 = 0xae89643f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 216 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 216 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 216 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 216 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_7 :
    Ripemd160.readLE32 patternedInput 220 = 0x421df8d3 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 220 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 220 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 220 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 220 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_8 :
    Ripemd160.readLE32 patternedInput 224 = 0xd6b18c67 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 224 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 224 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 224 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 224 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_9 :
    Ripemd160.readLE32 patternedInput 228 = 0x6a4520fb := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 228 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 228 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 228 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 228 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_10 :
    Ripemd160.readLE32 patternedInput 232 = 0xfed9b48f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 232 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 232 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 232 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 232 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_11 :
    Ripemd160.readLE32 patternedInput 236 = 0x926d4823 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 236 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 236 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 236 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 236 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_12 :
    Ripemd160.readLE32 patternedInput 240 = 0x2601dcb7 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 240 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 240 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 240 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 240 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_13 :
    Ripemd160.readLE32 patternedInput 244 = 0xba95704b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 244 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 244 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 244 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 244 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_14 :
    Ripemd160.readLE32 patternedInput 248 = 0x592904df := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 248 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 248 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 248 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 248 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_192_15 :
    Ripemd160.readLE32 patternedInput 252 = 0xedc8a37e := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 252 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 252 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 252 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 252 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem schedule3 : CompressionCorrect.schedule patternedInput 192 = block3 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_192_0]
  rw [read_192_1]
  rw [read_192_2]
  rw [read_192_3]
  rw [read_192_4]
  rw [read_192_5]
  rw [read_192_6]
  rw [read_192_7]
  rw [read_192_8]
  rw [read_192_9]
  rw [read_192_10]
  rw [read_192_11]
  rw [read_192_12]
  rw [read_192_13]
  rw [read_192_14]
  rw [read_192_15]
  decide

theorem compress3 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 192 =
      CompressionCorrect.normalizedCompress h block3 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule3]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
