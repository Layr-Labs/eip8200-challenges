import Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27InputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Spec

/-!
# `spec gen27Input` equals the stored digest

Proved against the challenge specification, not assumed: the two data blocks
are compressed from `H0`, then the padding tail block, and the final state is
emitted little-endian.

This module is a direct analogue of `Patterned128Digest.lean` (the 128-byte
patterned arm), retargeted at the generated vector #27 literal `gen27Input`.
-/

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27Digest

open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open Gen27InputData
/-- `gen27Input` schedules to `gen27Block0` at byte offset 0. -/
theorem schedule0 :
    CompressionCorrect.schedule gen27Input 0 = gen27Block0 := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl,
    gen27Input, gen27Block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide

/-- `gen27Input` schedules to `gen27Block1` at byte offset 64. -/
theorem schedule1 :
    CompressionCorrect.schedule gen27Input 64 = gen27Block1 := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl,
    gen27Input, gen27Block1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide

/-- Compressing block 0 from the IV yields `gen27H1`. -/
theorem step0 :
    CompressionCorrect.normalizedCompress Ripemd160.H0 gen27Block0 = gen27H1 := by
  decide

/-- Compressing block 1 from `gen27H1` yields `gen27H2`. -/
theorem step1 :
    CompressionCorrect.normalizedCompress gen27H1 gen27Block1 = gen27H2 := by
  decide

theorem hashAfter_two :
    SpecBridge.absorbBlocks Ripemd160.H0 gen27Input 0 2 = gen27H2 := by
  change Ripemd160.compressBlock
    (Ripemd160.compressBlock Ripemd160.H0 gen27Input 0) gen27Input 64 = gen27H2
  simp only [CompressionCorrect.compressBlock_eq_normalized,
    show CompressionCorrect.schedule gen27Input 0 = gen27Block0
      from schedule0,
    show CompressionCorrect.schedule gen27Input 64 = gen27Block1
      from schedule1,
    step0, step1]

private theorem lengthBytes_eq :
    Padding.lengthBytes gen27Input = ByteArray.mk #[0, 4, 0, 0, 0, 0, 0, 0] := by
  apply ByteArray.ext_getElem
  · rw [Padding.lengthBytes_size]
    decide
  · intro i hleft _hright
    have hi : i < 8 := by simpa only [Padding.lengthBytes_size] using hleft
    rw [Padding.lengthByte gen27Input i hi, gen27Input_size]
    interval_cases i <;>
      norm_num [ByteArray.getElem_eq_getElem_data, ByteArray.size] <;>
      decide

theorem paddedMessage_split :
    Padding.paddedMessage gen27Input = gen27Input ++ gen27Tail := by
  unfold Padding.paddedMessage
  rw [gen27Input_size, lengthBytes_eq]
  simp only [ByteArray.append_assoc]
  rfl

theorem read_tail0 (i : Nat) (hi : i < 16) :
    Ripemd160.readLE32 gen27Tail (i * 4) = gen27TailWords[i]! := by
  interval_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [gen27Tail, gen27TailWords, Ripemd160.readLE32,
        List.range', List.foldl, ByteArray.size,
        ByteArray.getElem_eq_getElem_data] <;>
    try (apply UInt32.eq_of_toBitVec_eq; decide)

theorem schedule_tail :
    CompressionCorrect.schedule gen27Tail 0 = gen27TailWords := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 gen27Tail (0 * 4) = gen27TailWords[0]! from read_tail0 0 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (1 * 4) = gen27TailWords[1]! from read_tail0 1 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (2 * 4) = gen27TailWords[2]! from read_tail0 2 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (3 * 4) = gen27TailWords[3]! from read_tail0 3 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (4 * 4) = gen27TailWords[4]! from read_tail0 4 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (5 * 4) = gen27TailWords[5]! from read_tail0 5 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (6 * 4) = gen27TailWords[6]! from read_tail0 6 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (7 * 4) = gen27TailWords[7]! from read_tail0 7 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (8 * 4) = gen27TailWords[8]! from read_tail0 8 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (9 * 4) = gen27TailWords[9]! from read_tail0 9 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (10 * 4) = gen27TailWords[10]! from read_tail0 10 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (11 * 4) = gen27TailWords[11]! from read_tail0 11 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (12 * 4) = gen27TailWords[12]! from read_tail0 12 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (13 * 4) = gen27TailWords[13]! from read_tail0 13 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (14 * 4) = gen27TailWords[14]! from read_tail0 14 (by omega)]
  rw [show Ripemd160.readLE32 gen27Tail (15 * 4) = gen27TailWords[15]! from read_tail0 15 (by omega)]
  decide

/-- Compressing the tail block from `gen27H2` yields the final state. -/
theorem step_tail :
    CompressionCorrect.normalizedCompress gen27H2 gen27TailWords = gen27FinalState := by
  decide

theorem hashAfter_three :
    SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage gen27Input) 0 3
      = gen27FinalState := by
  rw [paddedMessage_split]
  rw [show 3 = 2 + 1 from rfl,
    HashSpecBridge.absorbBlocks_append Ripemd160.H0 gen27Input gen27Tail 2 1 (by
      rw [gen27Input_size]), hashAfter_two]
  change Ripemd160.compressBlock gen27H2 gen27Tail 0 = gen27FinalState
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule_tail, step_tail]

theorem emit : SpecBridge.emitDigest gen27FinalState = gen27Digest := by
  unfold SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

theorem hash_gen27 : Ripemd160.hash gen27Input = gen27Digest := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  unfold SpecBridge.paddedHash
  rw [gen27Input_size]
  change SpecBridge.emitDigest
    (SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage gen27Input) 0 3)
      = gen27Digest
  rw [hashAfter_three, emit]

/-- The obligation the fast path needs: the stored 32-byte answer **is**
`spec gen27Input`. -/
theorem spec_gen27 : Challenge.Ripemd160.spec gen27Input = gen27PaddedDigest := by
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [hash_gen27]
  decide

#print axioms spec_gen27

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27Digest
