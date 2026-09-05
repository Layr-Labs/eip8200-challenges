import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestD

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

theorem read_0_0 :
    Ripemd160.readLE32 patternedInput 0 = 0x76512c07 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 0 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 0 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 0 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 0 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_1 :
    Ripemd160.readLE32 patternedInput 4 = 0x0ae5c09b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 4 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 4 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 4 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 4 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_2 :
    Ripemd160.readLE32 patternedInput 8 = 0x9e79542f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 8 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 8 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 8 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 8 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_3 :
    Ripemd160.readLE32 patternedInput 12 = 0x320de8c3 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 12 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 12 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 12 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 12 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_4 :
    Ripemd160.readLE32 patternedInput 16 = 0xc6a17c57 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 16 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 16 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 16 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 16 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_5 :
    Ripemd160.readLE32 patternedInput 20 = 0x5a3510eb := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 20 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 20 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 20 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 20 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_6 :
    Ripemd160.readLE32 patternedInput 24 = 0xeec9a47f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 24 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 24 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 24 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 24 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_7 :
    Ripemd160.readLE32 patternedInput 28 = 0x825d3813 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 28 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 28 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 28 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 28 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_8 :
    Ripemd160.readLE32 patternedInput 32 = 0x16f1cca7 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 32 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 32 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 32 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 32 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_9 :
    Ripemd160.readLE32 patternedInput 36 = 0xaa85603b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 36 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 36 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 36 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 36 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_10 :
    Ripemd160.readLE32 patternedInput 40 = 0x3e19f4cf := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 40 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 40 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 40 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 40 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_11 :
    Ripemd160.readLE32 patternedInput 44 = 0xd2ad8863 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 44 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 44 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 44 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 44 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_12 :
    Ripemd160.readLE32 patternedInput 48 = 0x66411cf7 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 48 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 48 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 48 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 48 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_13 :
    Ripemd160.readLE32 patternedInput 52 = 0xfad5b08b := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 52 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 52 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 52 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 52 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_14 :
    Ripemd160.readLE32 patternedInput 56 = 0x8e69441f := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 56 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 56 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 56 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 56 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_0_15 :
    Ripemd160.readLE32 patternedInput 60 = 0x22fdd8b3 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 60 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 60 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 60 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 60 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

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

theorem read_320_0 :
    Ripemd160.readLE32 patternedInput 320 = 0xc19c7752 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 320 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 320 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 320 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 320 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_1 :
    Ripemd160.readLE32 patternedInput 324 = 0x55300be6 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 324 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 324 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 324 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 324 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_2 :
    Ripemd160.readLE32 patternedInput 328 = 0xe9c49f7a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 328 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 328 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 328 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 328 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_3 :
    Ripemd160.readLE32 patternedInput 332 = 0x7d58330e := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 332 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 332 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 332 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 332 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_4 :
    Ripemd160.readLE32 patternedInput 336 = 0x11ecc7a2 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 336 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 336 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 336 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 336 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_5 :
    Ripemd160.readLE32 patternedInput 340 = 0xa5805b36 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 340 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 340 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 340 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 340 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_6 :
    Ripemd160.readLE32 patternedInput 344 = 0x3914efca := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 344 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 344 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 344 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 344 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_7 :
    Ripemd160.readLE32 patternedInput 348 = 0xcda8835e := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 348 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 348 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 348 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 348 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_8 :
    Ripemd160.readLE32 patternedInput 352 = 0x613c17f2 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 352 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 352 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 352 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 352 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_9 :
    Ripemd160.readLE32 patternedInput 356 = 0xf5d0ab86 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 356 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 356 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 356 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 356 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_10 :
    Ripemd160.readLE32 patternedInput 360 = 0x89643f1a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 360 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 360 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 360 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 360 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_11 :
    Ripemd160.readLE32 patternedInput 364 = 0x1df8d3ae := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 364 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 364 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 364 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 364 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_12 :
    Ripemd160.readLE32 patternedInput 368 = 0xb18c6742 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 368 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 368 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 368 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 368 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_13 :
    Ripemd160.readLE32 patternedInput 372 = 0x4520fbd6 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 372 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 372 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 372 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 372 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_14 :
    Ripemd160.readLE32 patternedInput 376 = 0xd9b48f6a := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 376 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 376 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 376 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 376 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_320_15 :
    Ripemd160.readLE32 patternedInput 380 = 0x6d4823fe := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 380 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 380 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 380 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 380 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

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

theorem read_640_0 :
    Ripemd160.readLE32 patternedInput 640 = 0x0ce7c29d := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 640 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 640 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 640 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 640 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_1 :
    Ripemd160.readLE32 patternedInput 644 = 0xa07b5631 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 644 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 644 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 644 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 644 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_2 :
    Ripemd160.readLE32 patternedInput 648 = 0x340feac5 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 648 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 648 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 648 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 648 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_3 :
    Ripemd160.readLE32 patternedInput 652 = 0xc8a37e59 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 652 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 652 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 652 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 652 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_4 :
    Ripemd160.readLE32 patternedInput 656 = 0x5c3712ed := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 656 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 656 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 656 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 656 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_5 :
    Ripemd160.readLE32 patternedInput 660 = 0xf0cba681 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 660 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 660 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 660 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 660 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_6 :
    Ripemd160.readLE32 patternedInput 664 = 0x845f3a15 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 664 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 664 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 664 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 664 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_7 :
    Ripemd160.readLE32 patternedInput 668 = 0x18f3cea9 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 668 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 668 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 668 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 668 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_8 :
    Ripemd160.readLE32 patternedInput 672 = 0xac87623d := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 672 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 672 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 672 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 672 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_9 :
    Ripemd160.readLE32 patternedInput 676 = 0x401bf6d1 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 676 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 676 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 676 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 676 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_10 :
    Ripemd160.readLE32 patternedInput 680 = 0xd4af8a65 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 680 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 680 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 680 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 680 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_11 :
    Ripemd160.readLE32 patternedInput 684 = 0x68431ef9 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 684 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 684 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 684 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 684 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_12 :
    Ripemd160.readLE32 patternedInput 688 = 0xfcd7b28d := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 688 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 688 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 688 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 688 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_13 :
    Ripemd160.readLE32 patternedInput 692 = 0x906b4621 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 692 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 692 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 692 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 692 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_14 :
    Ripemd160.readLE32 patternedInput 696 = 0x24ffdab5 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 696 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 696 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 696 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 696 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_640_15 :
    Ripemd160.readLE32 patternedInput 700 = 0xb8936e49 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 700 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 700 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 700 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 700 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_0 :
    Ripemd160.readLE32 patternedInput 704 = 0x4c2702dd := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 704 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 704 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 704 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 704 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_1 :
    Ripemd160.readLE32 patternedInput 708 = 0xe0bb9671 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 708 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 708 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 708 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 708 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_2 :
    Ripemd160.readLE32 patternedInput 712 = 0x744f2a05 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 712 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 712 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 712 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 712 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_3 :
    Ripemd160.readLE32 patternedInput 716 = 0x08e3be99 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 716 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 716 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 716 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 716 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_4 :
    Ripemd160.readLE32 patternedInput 720 = 0x9c77522d := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 720 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 720 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 720 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 720 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_5 :
    Ripemd160.readLE32 patternedInput 724 = 0x300be6c1 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 724 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 724 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 724 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 724 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_6 :
    Ripemd160.readLE32 patternedInput 728 = 0xc49f7a55 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 728 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 728 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 728 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 728 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_7 :
    Ripemd160.readLE32 patternedInput 732 = 0x58330ee9 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 732 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 732 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 732 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 732 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_8 :
    Ripemd160.readLE32 patternedInput 736 = 0xecc7a27d := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 736 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 736 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 736 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 736 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_9 :
    Ripemd160.readLE32 patternedInput 740 = 0x805b3611 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 740 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 740 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 740 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 740 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_10 :
    Ripemd160.readLE32 patternedInput 744 = 0x14efcaa5 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 744 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 744 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 744 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 744 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_11 :
    Ripemd160.readLE32 patternedInput 748 = 0xa8835e39 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 748 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 748 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 748 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 748 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_12 :
    Ripemd160.readLE32 patternedInput 752 = 0x4722fdcd := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 752 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 752 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 752 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 752 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_13 :
    Ripemd160.readLE32 patternedInput 756 = 0xdbb6916c := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 756 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 756 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 756 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 756 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_14 :
    Ripemd160.readLE32 patternedInput 760 = 0x6f4a2500 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 760 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 760 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 760 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 760 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_704_15 :
    Ripemd160.readLE32 patternedInput 764 = 0x03deb994 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 764 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 764 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 764 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 764 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

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

theorem read_832_0 :
    Ripemd160.readLE32 patternedInput 832 = 0xd7b28d68 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 832 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 832 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 832 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 832 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_1 :
    Ripemd160.readLE32 patternedInput 836 = 0x6b4621fc := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 836 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 836 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 836 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 836 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_2 :
    Ripemd160.readLE32 patternedInput 840 = 0xffdab590 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 840 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 840 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 840 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 840 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_3 :
    Ripemd160.readLE32 patternedInput 844 = 0x936e4924 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 844 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 844 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 844 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 844 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_4 :
    Ripemd160.readLE32 patternedInput 848 = 0x2702ddb8 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 848 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 848 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 848 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 848 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_5 :
    Ripemd160.readLE32 patternedInput 852 = 0xbb96714c := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 852 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 852 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 852 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 852 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_6 :
    Ripemd160.readLE32 patternedInput 856 = 0x4f2a05e0 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 856 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 856 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 856 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 856 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_7 :
    Ripemd160.readLE32 patternedInput 860 = 0xe3be9974 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 860 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 860 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 860 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 860 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_8 :
    Ripemd160.readLE32 patternedInput 864 = 0x77522d08 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 864 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 864 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 864 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 864 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_9 :
    Ripemd160.readLE32 patternedInput 868 = 0x0be6c19c := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 868 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 868 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 868 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 868 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_10 :
    Ripemd160.readLE32 patternedInput 872 = 0x9f7a5530 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 872 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 872 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 872 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 872 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_11 :
    Ripemd160.readLE32 patternedInput 876 = 0x330ee9c4 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 876 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 876 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 876 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 876 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_12 :
    Ripemd160.readLE32 patternedInput 880 = 0xc7a27d58 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 880 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 880 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 880 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 880 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_13 :
    Ripemd160.readLE32 patternedInput 884 = 0x5b3611ec := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 884 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 884 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 884 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 884 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_14 :
    Ripemd160.readLE32 patternedInput 888 = 0xefcaa580 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 888 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 888 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 888 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 888 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

theorem read_832_15 :
    Ripemd160.readLE32 patternedInput 892 = 0x835e3914 := by
  unfold Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : 892 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h1 : 892 + 1 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h2 : 892 + 2 < patternedInput.size := by
    rw [patternedInput_size]; omega
  have h3 : 892 + 3 < patternedInput.size := by
    rw [patternedInput_size]; omega
  simp only [Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul]
  rw [dif_pos h0, dif_pos h1, dif_pos h2, dif_pos h3,
    patternedInput_getElem _ h0,
    patternedInput_getElem _ h1,
    patternedInput_getElem _ h2,
    patternedInput_getElem _ h3]
  decide

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

theorem schedule0 : CompressionCorrect.schedule patternedInput 0 = block0 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_0_0]
  rw [read_0_1]
  rw [read_0_2]
  rw [read_0_3]
  rw [read_0_4]
  rw [read_0_5]
  rw [read_0_6]
  rw [read_0_7]
  rw [read_0_8]
  rw [read_0_9]
  rw [read_0_10]
  rw [read_0_11]
  rw [read_0_12]
  rw [read_0_13]
  rw [read_0_14]
  rw [read_0_15]
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

theorem schedule5 : CompressionCorrect.schedule patternedInput 320 = block5 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_320_0]
  rw [read_320_1]
  rw [read_320_2]
  rw [read_320_3]
  rw [read_320_4]
  rw [read_320_5]
  rw [read_320_6]
  rw [read_320_7]
  rw [read_320_8]
  rw [read_320_9]
  rw [read_320_10]
  rw [read_320_11]
  rw [read_320_12]
  rw [read_320_13]
  rw [read_320_14]
  rw [read_320_15]
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

theorem schedule10 : CompressionCorrect.schedule patternedInput 640 = block10 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_640_0]
  rw [read_640_1]
  rw [read_640_2]
  rw [read_640_3]
  rw [read_640_4]
  rw [read_640_5]
  rw [read_640_6]
  rw [read_640_7]
  rw [read_640_8]
  rw [read_640_9]
  rw [read_640_10]
  rw [read_640_11]
  rw [read_640_12]
  rw [read_640_13]
  rw [read_640_14]
  rw [read_640_15]
  decide

theorem schedule11 : CompressionCorrect.schedule patternedInput 704 = block11 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_704_0]
  rw [read_704_1]
  rw [read_704_2]
  rw [read_704_3]
  rw [read_704_4]
  rw [read_704_5]
  rw [read_704_6]
  rw [read_704_7]
  rw [read_704_8]
  rw [read_704_9]
  rw [read_704_10]
  rw [read_704_11]
  rw [read_704_12]
  rw [read_704_13]
  rw [read_704_14]
  rw [read_704_15]
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

theorem schedule13 : CompressionCorrect.schedule patternedInput 832 = block13 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [read_832_0]
  rw [read_832_1]
  rw [read_832_2]
  rw [read_832_3]
  rw [read_832_4]
  rw [read_832_5]
  rw [read_832_6]
  rw [read_832_7]
  rw [read_832_8]
  rw [read_832_9]
  rw [read_832_10]
  rw [read_832_11]
  rw [read_832_12]
  rw [read_832_13]
  rw [read_832_14]
  rw [read_832_15]
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

theorem read_final (i : Nat) (hi : i < 16) :
    Ripemd160.readLE32 finalBlock (i * 4) = finalWords[i]! := by
  interval_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [finalBlock, finalWords, Ripemd160.readLE32,
        List.range', List.foldl, ByteArray.size,
        ByteArray.getElem_eq_getElem_data] <;>
    try (apply UInt32.eq_of_toBitVec_eq; decide)

theorem schedule_final : CompressionCorrect.schedule finalBlock 0 = finalWords := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 finalBlock (0 * 4) = finalWords[0]! from read_final 0 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (1 * 4) = finalWords[1]! from read_final 1 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (2 * 4) = finalWords[2]! from read_final 2 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (3 * 4) = finalWords[3]! from read_final 3 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (4 * 4) = finalWords[4]! from read_final 4 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (5 * 4) = finalWords[5]! from read_final 5 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (6 * 4) = finalWords[6]! from read_final 6 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (7 * 4) = finalWords[7]! from read_final 7 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (8 * 4) = finalWords[8]! from read_final 8 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (9 * 4) = finalWords[9]! from read_final 9 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (10 * 4) = finalWords[10]! from read_final 10 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (11 * 4) = finalWords[11]! from read_final 11 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (12 * 4) = finalWords[12]! from read_final 12 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (13 * 4) = finalWords[13]! from read_final 13 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (14 * 4) = finalWords[14]! from read_final 14 (by omega)]
  rw [show Ripemd160.readLE32 finalBlock (15 * 4) = finalWords[15]! from read_final 15 (by omega)]
  decide


theorem compress0 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 0 =
      CompressionCorrect.normalizedCompress h block0 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule0]
theorem compress1 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 64 =
      CompressionCorrect.normalizedCompress h block1 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule1]
theorem compress2 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 128 =
      CompressionCorrect.normalizedCompress h block2 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule2]
theorem compress3 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 192 =
      CompressionCorrect.normalizedCompress h block3 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule3]
theorem compress4 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 256 =
      CompressionCorrect.normalizedCompress h block4 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule4]
theorem compress5 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 320 =
      CompressionCorrect.normalizedCompress h block5 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule5]
theorem compress6 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 384 =
      CompressionCorrect.normalizedCompress h block6 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule6]
theorem compress7 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 448 =
      CompressionCorrect.normalizedCompress h block7 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule7]
theorem compress8 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 512 =
      CompressionCorrect.normalizedCompress h block8 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule8]
theorem compress9 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 576 =
      CompressionCorrect.normalizedCompress h block9 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule9]
theorem compress10 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 640 =
      CompressionCorrect.normalizedCompress h block10 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule10]
theorem compress11 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 704 =
      CompressionCorrect.normalizedCompress h block11 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule11]
theorem compress12 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 768 =
      CompressionCorrect.normalizedCompress h block12 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule12]
theorem compress13 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 832 =
      CompressionCorrect.normalizedCompress h block13 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule13]
theorem compress14 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 896 =
      CompressionCorrect.normalizedCompress h block14 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule14]
theorem compress_final (h : Array UInt32) :
    Ripemd160.compressBlock h finalBlock 0 =
      CompressionCorrect.normalizedCompress h finalWords := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule_final]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
