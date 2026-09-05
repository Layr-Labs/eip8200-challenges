import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

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

theorem compress10 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 640 =
      CompressionCorrect.normalizedCompress h block10 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule10]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
