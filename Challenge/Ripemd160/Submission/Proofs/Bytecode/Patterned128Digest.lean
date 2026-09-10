import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Data
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSchedulesA

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
set_option linter.unnecessarySeqFocus false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Digest

open EvmSemantics EvmSemantics.Crypto
open Patterned128Data

def tailWords0 : Array UInt32 :=
  #[0x80, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x400, 0x0]

def finalHash : Array UInt32 :=
  #[0x14afdf28, 0xf45399ed, 0x56bb7a9c, 0xc6d00813, 0x79c1c44b]

def targetDigest : ByteArray := SpecBridge.emitDigest finalHash

def paddedDigest : ByteArray := ByteArray.mk #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0x28, 0xdf, 0xaf, 0x14, 0xed, 0x99, 0x53, 0xf4, 0x9c, 0x7a,
  0xbb, 0x56, 0x13, 0x08, 0xd0, 0xc6, 0x4b, 0xc4, 0xc1, 0x79]

def paddedDigestWord : UInt256 :=
  0x00000000000000000000000028dfaf14ed9953f49c7abb561308d0c64bc4c179

def finalTail : ByteArray := ByteArray.mk #[
  0x80, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 4, 0, 0, 0, 0, 0, 0]

@[simp] theorem finalTail_size : finalTail.size = 64 := by decide

private theorem lengthBytes_eq :
    Padding.lengthBytes data = ByteArray.mk #[0, 4, 0, 0, 0, 0, 0, 0] := by
  apply ByteArray.ext_getElem
  · rw [Padding.lengthBytes_size]
    decide
  · intro i hleft _hright
    have hi : i < 8 := by simpa only [Padding.lengthBytes_size] using hleft
    rw [Padding.lengthByte data i hi, data_size]
    interval_cases i <;>
      norm_num [ByteArray.getElem_eq_getElem_data, ByteArray.size] <;>
      decide

theorem paddedMessage_split : Padding.paddedMessage data = data ++ finalTail := by
  unfold Padding.paddedMessage
  rw [data_size, lengthBytes_eq]
  simp only [ByteArray.append_assoc]
  rfl

private theorem compress_data (h : Array UInt32) (off : Nat) (hoff : off + 64 ≤ 128) :
    Ripemd160.compressBlock h data off =
      Ripemd160.compressBlock h PatternedInputData.patternedInput off := by
  apply HashSpecBridge.compressBlock_eq_of_readLE32
  intro i hi
  apply HashSpecBridge.readLE32_eq_of_byte
  intro j hj
  have hdata : off + i * 4 + j < data.size := by rw [data_size]; omega
  have hpattern : off + i * 4 + j < PatternedInputData.patternedInput.size := by
    rw [PatternedInputData.patternedInput_size]; omega
  rw [dif_pos hdata, dif_pos hpattern,
    data_getElem, PatternedInputData.patternedInput_getElem]

theorem hashAfter_two : SpecBridge.absorbBlocks Ripemd160.H0 data 0 2 =
    PatternedDigest.H2 := by
  change Ripemd160.compressBlock
    (Ripemd160.compressBlock PatternedDigest.H0 data 0) data 64 =
      PatternedDigest.H2
  rw [compress_data _ 0 (by omega), compress_data _ 64 (by omega)]
  simp only [CompressionCorrect.compressBlock_eq_normalized,
    PatternedDigest.schedule0, PatternedDigest.schedule1,
    PatternedDigestA.step0, PatternedDigestA.step1]

theorem read_tail0 (i : Nat) (hi : i < 16) :
    Ripemd160.readLE32 finalTail (i * 4) = tailWords0[i]! := by
  interval_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [finalTail, tailWords0, Ripemd160.readLE32,
        List.range', List.foldl, ByteArray.size,
        ByteArray.getElem_eq_getElem_data] <;>
    try (apply UInt32.eq_of_toBitVec_eq; decide)

theorem schedule_tail0 : CompressionCorrect.schedule finalTail 0 = tailWords0 := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 finalTail (0 * 4) = tailWords0[0]! from read_tail0 0 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (1 * 4) = tailWords0[1]! from read_tail0 1 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (2 * 4) = tailWords0[2]! from read_tail0 2 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (3 * 4) = tailWords0[3]! from read_tail0 3 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (4 * 4) = tailWords0[4]! from read_tail0 4 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (5 * 4) = tailWords0[5]! from read_tail0 5 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (6 * 4) = tailWords0[6]! from read_tail0 6 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (7 * 4) = tailWords0[7]! from read_tail0 7 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (8 * 4) = tailWords0[8]! from read_tail0 8 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (9 * 4) = tailWords0[9]! from read_tail0 9 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (10 * 4) = tailWords0[10]! from read_tail0 10 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (11 * 4) = tailWords0[11]! from read_tail0 11 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (12 * 4) = tailWords0[12]! from read_tail0 12 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (13 * 4) = tailWords0[13]! from read_tail0 13 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (14 * 4) = tailWords0[14]! from read_tail0 14 (by omega)]
  rw [show Ripemd160.readLE32 finalTail (15 * 4) = tailWords0[15]! from read_tail0 15 (by omega)]
  decide

theorem step_tail : CompressionCorrect.normalizedCompress PatternedDigest.H2 tailWords0 =
    finalHash := by decide

theorem hashAfter_three :
    SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data) 0 3 =
      finalHash := by
  rw [paddedMessage_split]
  rw [show 3 = 2 + 1 from rfl,
    HashSpecBridge.absorbBlocks_append Ripemd160.H0 data finalTail 2 1 (by
      rw [data_size]), hashAfter_two]
  change Ripemd160.compressBlock PatternedDigest.H2 finalTail 0 = finalHash
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule_tail0, step_tail]

theorem targetDigest_eq_literal : targetDigest = ByteArray.mk #[
    0x28, 0xdf, 0xaf, 0x14, 0xed, 0x99, 0x53, 0xf4, 0x9c, 0x7a,
    0xbb, 0x56, 0x13, 0x08, 0xd0, 0xc6, 0x4b, 0xc4, 0xc1, 0x79] := by
  unfold targetDigest SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

@[simp] theorem targetDigest_size : targetDigest.size = 20 := by
  rw [targetDigest_eq_literal]
  decide

@[simp] theorem paddedDigest_size : paddedDigest.size = 32 := by decide

theorem hash_data_eq : Ripemd160.hash data = targetDigest := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  unfold SpecBridge.paddedHash
  rw [data_size]
  change SpecBridge.emitDigest
    (SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data) 0 3) = targetDigest
  rw [hashAfter_three]
  rfl

theorem spec_data_eq : Challenge.Ripemd160.spec data = paddedDigest := by
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [hash_data_eq, targetDigest_eq_literal]
  decide

theorem wordBytes_eq_paddedDigest :
    Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32 = paddedDigest := by
  rw [Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Digest

#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Digest.step_tail
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Digest.spec_data_eq
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Digest.wordBytes_eq_paddedDigest
