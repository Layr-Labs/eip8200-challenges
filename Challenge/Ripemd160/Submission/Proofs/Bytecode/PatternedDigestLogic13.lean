import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest

open EvmSemantics.Crypto PatternedInputData

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

theorem compress13 (h : Array UInt32) :
    Ripemd160.compressBlock h patternedInput 832 =
      CompressionCorrect.normalizedCompress h block13 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule13]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigest
