import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleFastP1000
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock10
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock16
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock18
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock19
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock21
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock24
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock25
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock26
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock27
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock28
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock29
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock30
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock31
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock32
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock33
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock34

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode FastSchedule

def statesP1000 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn10
  | 1 => HOut10
  | 2 => HOut16
  | 3 => HOut18
  | 4 => HOut19
  | 5 => HOut21
  | 6 => HOut24
  | 7 => HOut25
  | 8 => HOut26
  | 9 => HOut27
  | 10 => HOut28
  | 11 => HOut29
  | 12 => HOut30
  | 13 => HOut31
  | 14 => HOut32
  | 15 => HOut33
  | _ => HOut34

theorem stepP1000_0 :
    Ripemd160.compressBlock HIn10 (Padding.paddedMessage inputP1000) 0 =
      HOut10 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_0, block10]

theorem stepP1000_1 :
    Ripemd160.compressBlock HIn16 (Padding.paddedMessage inputP1000) 64 =
      HOut16 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_1, block16]

theorem stepP1000_2 :
    Ripemd160.compressBlock HIn18 (Padding.paddedMessage inputP1000) 128 =
      HOut18 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_2, block18]

theorem stepP1000_3 :
    Ripemd160.compressBlock HIn19 (Padding.paddedMessage inputP1000) 192 =
      HOut19 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_3, block19]

theorem stepP1000_4 :
    Ripemd160.compressBlock HIn21 (Padding.paddedMessage inputP1000) 256 =
      HOut21 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_4, block21]

theorem stepP1000_5 :
    Ripemd160.compressBlock HIn24 (Padding.paddedMessage inputP1000) 320 =
      HOut24 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_5, block24]

theorem stepP1000_6 :
    Ripemd160.compressBlock HIn25 (Padding.paddedMessage inputP1000) 384 =
      HOut25 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_6, block25]

theorem stepP1000_7 :
    Ripemd160.compressBlock HIn26 (Padding.paddedMessage inputP1000) 448 =
      HOut26 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_7, block26]

theorem stepP1000_8 :
    Ripemd160.compressBlock HIn27 (Padding.paddedMessage inputP1000) 512 =
      HOut27 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_8, block27]

theorem stepP1000_9 :
    Ripemd160.compressBlock HIn28 (Padding.paddedMessage inputP1000) 576 =
      HOut28 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_9, block28]

theorem stepP1000_10 :
    Ripemd160.compressBlock HIn29 (Padding.paddedMessage inputP1000) 640 =
      HOut29 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_10, block29]

theorem stepP1000_11 :
    Ripemd160.compressBlock HIn30 (Padding.paddedMessage inputP1000) 704 =
      HOut30 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_11, block30]

theorem stepP1000_12 :
    Ripemd160.compressBlock HIn31 (Padding.paddedMessage inputP1000) 768 =
      HOut31 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_12, block31]

theorem stepP1000_13 :
    Ripemd160.compressBlock HIn32 (Padding.paddedMessage inputP1000) 832 =
      HOut32 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_13, block32]

theorem stepP1000_14 :
    Ripemd160.compressBlock HIn33 (Padding.paddedMessage inputP1000) 896 =
      HOut33 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_14, block33]

theorem stepP1000_15 :
    Ripemd160.compressBlock HIn34 (Padding.paddedMessage inputP1000) 960 =
      HOut34 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1000_15, block34]

theorem spec_P1000 : spec inputP1000 = expectedP1000 := by
  apply spec_of_steps inputP1000 expectedP1000 statesP1000 16
  · decide
  · rfl
  · intro i hi
    interval_cases i <;> first
      | exact stepP1000_0
      | exact stepP1000_1
      | exact stepP1000_2
      | exact stepP1000_3
      | exact stepP1000_4
      | exact stepP1000_5
      | exact stepP1000_6
      | exact stepP1000_7
      | exact stepP1000_8
      | exact stepP1000_9
      | exact stepP1000_10
      | exact stepP1000_11
      | exact stepP1000_12
      | exact stepP1000_13
      | exact stepP1000_14
      | exact stepP1000_15
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo
