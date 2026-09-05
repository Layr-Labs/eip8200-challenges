import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

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

theorem compress11 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 704 =
      CompressionCorrect.normalizedCompress h block11 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule11]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
