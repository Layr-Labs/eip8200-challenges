import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Digest

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.all false
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Digest

open EvmSemantics.Crypto Patterned376InputData

theorem schedule0 : CompressionCorrect.schedule paddedLiteral 0 = block0 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : Ripemd160.readLE32 paddedLiteral (0 + 0 * 4) = block0[0]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h1 : Ripemd160.readLE32 paddedLiteral (0 + 1 * 4) = block0[1]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h2 : Ripemd160.readLE32 paddedLiteral (0 + 2 * 4) = block0[2]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h3 : Ripemd160.readLE32 paddedLiteral (0 + 3 * 4) = block0[3]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h4 : Ripemd160.readLE32 paddedLiteral (0 + 4 * 4) = block0[4]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h5 : Ripemd160.readLE32 paddedLiteral (0 + 5 * 4) = block0[5]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h6 : Ripemd160.readLE32 paddedLiteral (0 + 6 * 4) = block0[6]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h7 : Ripemd160.readLE32 paddedLiteral (0 + 7 * 4) = block0[7]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h8 : Ripemd160.readLE32 paddedLiteral (0 + 8 * 4) = block0[8]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h9 : Ripemd160.readLE32 paddedLiteral (0 + 9 * 4) = block0[9]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h10 : Ripemd160.readLE32 paddedLiteral (0 + 10 * 4) = block0[10]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h11 : Ripemd160.readLE32 paddedLiteral (0 + 11 * 4) = block0[11]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h12 : Ripemd160.readLE32 paddedLiteral (0 + 12 * 4) = block0[12]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h13 : Ripemd160.readLE32 paddedLiteral (0 + 13 * 4) = block0[13]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h14 : Ripemd160.readLE32 paddedLiteral (0 + 14 * 4) = block0[14]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h15 : Ripemd160.readLE32 paddedLiteral (0 + 15 * 4) = block0[15]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  rw [h0]
  rw [h1]
  rw [h2]
  rw [h3]
  rw [h4]
  rw [h5]
  rw [h6]
  rw [h7]
  rw [h8]
  rw [h9]
  rw [h10]
  rw [h11]
  rw [h12]
  rw [h13]
  rw [h14]
  rw [h15]
  decide
theorem schedule1 : CompressionCorrect.schedule paddedLiteral 64 = block1 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : Ripemd160.readLE32 paddedLiteral (64 + 0 * 4) = block1[0]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h1 : Ripemd160.readLE32 paddedLiteral (64 + 1 * 4) = block1[1]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h2 : Ripemd160.readLE32 paddedLiteral (64 + 2 * 4) = block1[2]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h3 : Ripemd160.readLE32 paddedLiteral (64 + 3 * 4) = block1[3]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h4 : Ripemd160.readLE32 paddedLiteral (64 + 4 * 4) = block1[4]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h5 : Ripemd160.readLE32 paddedLiteral (64 + 5 * 4) = block1[5]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h6 : Ripemd160.readLE32 paddedLiteral (64 + 6 * 4) = block1[6]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h7 : Ripemd160.readLE32 paddedLiteral (64 + 7 * 4) = block1[7]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h8 : Ripemd160.readLE32 paddedLiteral (64 + 8 * 4) = block1[8]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h9 : Ripemd160.readLE32 paddedLiteral (64 + 9 * 4) = block1[9]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h10 : Ripemd160.readLE32 paddedLiteral (64 + 10 * 4) = block1[10]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h11 : Ripemd160.readLE32 paddedLiteral (64 + 11 * 4) = block1[11]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h12 : Ripemd160.readLE32 paddedLiteral (64 + 12 * 4) = block1[12]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h13 : Ripemd160.readLE32 paddedLiteral (64 + 13 * 4) = block1[13]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h14 : Ripemd160.readLE32 paddedLiteral (64 + 14 * 4) = block1[14]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h15 : Ripemd160.readLE32 paddedLiteral (64 + 15 * 4) = block1[15]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  rw [h0]
  rw [h1]
  rw [h2]
  rw [h3]
  rw [h4]
  rw [h5]
  rw [h6]
  rw [h7]
  rw [h8]
  rw [h9]
  rw [h10]
  rw [h11]
  rw [h12]
  rw [h13]
  rw [h14]
  rw [h15]
  decide
theorem schedule2 : CompressionCorrect.schedule paddedLiteral 128 = block2 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : Ripemd160.readLE32 paddedLiteral (128 + 0 * 4) = block2[0]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h1 : Ripemd160.readLE32 paddedLiteral (128 + 1 * 4) = block2[1]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h2 : Ripemd160.readLE32 paddedLiteral (128 + 2 * 4) = block2[2]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h3 : Ripemd160.readLE32 paddedLiteral (128 + 3 * 4) = block2[3]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h4 : Ripemd160.readLE32 paddedLiteral (128 + 4 * 4) = block2[4]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h5 : Ripemd160.readLE32 paddedLiteral (128 + 5 * 4) = block2[5]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h6 : Ripemd160.readLE32 paddedLiteral (128 + 6 * 4) = block2[6]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h7 : Ripemd160.readLE32 paddedLiteral (128 + 7 * 4) = block2[7]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h8 : Ripemd160.readLE32 paddedLiteral (128 + 8 * 4) = block2[8]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h9 : Ripemd160.readLE32 paddedLiteral (128 + 9 * 4) = block2[9]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h10 : Ripemd160.readLE32 paddedLiteral (128 + 10 * 4) = block2[10]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h11 : Ripemd160.readLE32 paddedLiteral (128 + 11 * 4) = block2[11]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h12 : Ripemd160.readLE32 paddedLiteral (128 + 12 * 4) = block2[12]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h13 : Ripemd160.readLE32 paddedLiteral (128 + 13 * 4) = block2[13]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h14 : Ripemd160.readLE32 paddedLiteral (128 + 14 * 4) = block2[14]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h15 : Ripemd160.readLE32 paddedLiteral (128 + 15 * 4) = block2[15]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  rw [h0]
  rw [h1]
  rw [h2]
  rw [h3]
  rw [h4]
  rw [h5]
  rw [h6]
  rw [h7]
  rw [h8]
  rw [h9]
  rw [h10]
  rw [h11]
  rw [h12]
  rw [h13]
  rw [h14]
  rw [h15]
  decide
theorem schedule3 : CompressionCorrect.schedule paddedLiteral 192 = block3 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : Ripemd160.readLE32 paddedLiteral (192 + 0 * 4) = block3[0]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h1 : Ripemd160.readLE32 paddedLiteral (192 + 1 * 4) = block3[1]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h2 : Ripemd160.readLE32 paddedLiteral (192 + 2 * 4) = block3[2]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h3 : Ripemd160.readLE32 paddedLiteral (192 + 3 * 4) = block3[3]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h4 : Ripemd160.readLE32 paddedLiteral (192 + 4 * 4) = block3[4]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h5 : Ripemd160.readLE32 paddedLiteral (192 + 5 * 4) = block3[5]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h6 : Ripemd160.readLE32 paddedLiteral (192 + 6 * 4) = block3[6]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h7 : Ripemd160.readLE32 paddedLiteral (192 + 7 * 4) = block3[7]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h8 : Ripemd160.readLE32 paddedLiteral (192 + 8 * 4) = block3[8]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h9 : Ripemd160.readLE32 paddedLiteral (192 + 9 * 4) = block3[9]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h10 : Ripemd160.readLE32 paddedLiteral (192 + 10 * 4) = block3[10]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h11 : Ripemd160.readLE32 paddedLiteral (192 + 11 * 4) = block3[11]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h12 : Ripemd160.readLE32 paddedLiteral (192 + 12 * 4) = block3[12]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h13 : Ripemd160.readLE32 paddedLiteral (192 + 13 * 4) = block3[13]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h14 : Ripemd160.readLE32 paddedLiteral (192 + 14 * 4) = block3[14]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h15 : Ripemd160.readLE32 paddedLiteral (192 + 15 * 4) = block3[15]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block3, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  rw [h0]
  rw [h1]
  rw [h2]
  rw [h3]
  rw [h4]
  rw [h5]
  rw [h6]
  rw [h7]
  rw [h8]
  rw [h9]
  rw [h10]
  rw [h11]
  rw [h12]
  rw [h13]
  rw [h14]
  rw [h15]
  decide
theorem schedule4 : CompressionCorrect.schedule paddedLiteral 256 = block4 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : Ripemd160.readLE32 paddedLiteral (256 + 0 * 4) = block4[0]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h1 : Ripemd160.readLE32 paddedLiteral (256 + 1 * 4) = block4[1]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h2 : Ripemd160.readLE32 paddedLiteral (256 + 2 * 4) = block4[2]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h3 : Ripemd160.readLE32 paddedLiteral (256 + 3 * 4) = block4[3]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h4 : Ripemd160.readLE32 paddedLiteral (256 + 4 * 4) = block4[4]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h5 : Ripemd160.readLE32 paddedLiteral (256 + 5 * 4) = block4[5]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h6 : Ripemd160.readLE32 paddedLiteral (256 + 6 * 4) = block4[6]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h7 : Ripemd160.readLE32 paddedLiteral (256 + 7 * 4) = block4[7]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h8 : Ripemd160.readLE32 paddedLiteral (256 + 8 * 4) = block4[8]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h9 : Ripemd160.readLE32 paddedLiteral (256 + 9 * 4) = block4[9]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h10 : Ripemd160.readLE32 paddedLiteral (256 + 10 * 4) = block4[10]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h11 : Ripemd160.readLE32 paddedLiteral (256 + 11 * 4) = block4[11]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h12 : Ripemd160.readLE32 paddedLiteral (256 + 12 * 4) = block4[12]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h13 : Ripemd160.readLE32 paddedLiteral (256 + 13 * 4) = block4[13]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h14 : Ripemd160.readLE32 paddedLiteral (256 + 14 * 4) = block4[14]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h15 : Ripemd160.readLE32 paddedLiteral (256 + 15 * 4) = block4[15]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block4, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  rw [h0]
  rw [h1]
  rw [h2]
  rw [h3]
  rw [h4]
  rw [h5]
  rw [h6]
  rw [h7]
  rw [h8]
  rw [h9]
  rw [h10]
  rw [h11]
  rw [h12]
  rw [h13]
  rw [h14]
  rw [h15]
  decide
theorem schedule5 : CompressionCorrect.schedule paddedLiteral 320 = block5 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : Ripemd160.readLE32 paddedLiteral (320 + 0 * 4) = block5[0]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h1 : Ripemd160.readLE32 paddedLiteral (320 + 1 * 4) = block5[1]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h2 : Ripemd160.readLE32 paddedLiteral (320 + 2 * 4) = block5[2]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h3 : Ripemd160.readLE32 paddedLiteral (320 + 3 * 4) = block5[3]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h4 : Ripemd160.readLE32 paddedLiteral (320 + 4 * 4) = block5[4]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h5 : Ripemd160.readLE32 paddedLiteral (320 + 5 * 4) = block5[5]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h6 : Ripemd160.readLE32 paddedLiteral (320 + 6 * 4) = block5[6]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h7 : Ripemd160.readLE32 paddedLiteral (320 + 7 * 4) = block5[7]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h8 : Ripemd160.readLE32 paddedLiteral (320 + 8 * 4) = block5[8]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h9 : Ripemd160.readLE32 paddedLiteral (320 + 9 * 4) = block5[9]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h10 : Ripemd160.readLE32 paddedLiteral (320 + 10 * 4) = block5[10]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h11 : Ripemd160.readLE32 paddedLiteral (320 + 11 * 4) = block5[11]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h12 : Ripemd160.readLE32 paddedLiteral (320 + 12 * 4) = block5[12]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h13 : Ripemd160.readLE32 paddedLiteral (320 + 13 * 4) = block5[13]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h14 : Ripemd160.readLE32 paddedLiteral (320 + 14 * 4) = block5[14]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h15 : Ripemd160.readLE32 paddedLiteral (320 + 15 * 4) = block5[15]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block5, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  rw [h0]
  rw [h1]
  rw [h2]
  rw [h3]
  rw [h4]
  rw [h5]
  rw [h6]
  rw [h7]
  rw [h8]
  rw [h9]
  rw [h10]
  rw [h11]
  rw [h12]
  rw [h13]
  rw [h14]
  rw [h15]
  decide
theorem schedule6 : CompressionCorrect.schedule paddedLiteral 384 = block6 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  have h0 : Ripemd160.readLE32 paddedLiteral (384 + 0 * 4) = block6[0]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h1 : Ripemd160.readLE32 paddedLiteral (384 + 1 * 4) = block6[1]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h2 : Ripemd160.readLE32 paddedLiteral (384 + 2 * 4) = block6[2]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h3 : Ripemd160.readLE32 paddedLiteral (384 + 3 * 4) = block6[3]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h4 : Ripemd160.readLE32 paddedLiteral (384 + 4 * 4) = block6[4]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h5 : Ripemd160.readLE32 paddedLiteral (384 + 5 * 4) = block6[5]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h6 : Ripemd160.readLE32 paddedLiteral (384 + 6 * 4) = block6[6]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h7 : Ripemd160.readLE32 paddedLiteral (384 + 7 * 4) = block6[7]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h8 : Ripemd160.readLE32 paddedLiteral (384 + 8 * 4) = block6[8]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h9 : Ripemd160.readLE32 paddedLiteral (384 + 9 * 4) = block6[9]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h10 : Ripemd160.readLE32 paddedLiteral (384 + 10 * 4) = block6[10]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h11 : Ripemd160.readLE32 paddedLiteral (384 + 11 * 4) = block6[11]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h12 : Ripemd160.readLE32 paddedLiteral (384 + 12 * 4) = block6[12]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h13 : Ripemd160.readLE32 paddedLiteral (384 + 13 * 4) = block6[13]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h14 : Ripemd160.readLE32 paddedLiteral (384 + 14 * 4) = block6[14]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  have h15 : Ripemd160.readLE32 paddedLiteral (384 + 15 * 4) = block6[15]! := by
    unfold Ripemd160.readLE32
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
    norm_num (config := { maxSteps := 1000000 })
      [paddedLiteral, block6, ByteArray.size, ByteArray.getElem_eq_getElem_data]
    try (apply UInt32.eq_of_toBitVec_eq; decide)
  rw [h0]
  rw [h1]
  rw [h2]
  rw [h3]
  rw [h4]
  rw [h5]
  rw [h6]
  rw [h7]
  rw [h8]
  rw [h9]
  rw [h10]
  rw [h11]
  rw [h12]
  rw [h13]
  rw [h14]
  rw [h15]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Digest
