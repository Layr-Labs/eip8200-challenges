import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleP376
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock10
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock16
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock18
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock19
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock21
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock22
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock23

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

def statesP376 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn10
  | 1 => HOut10
  | 2 => HOut16
  | 3 => HOut18
  | 4 => HOut19
  | 5 => HOut21
  | 6 => HOut22
  | _ => HOut23

theorem stepP376_0 :
    Ripemd160.compressBlock HIn10 (Padding.paddedMessage inputP376) 0 =
      HOut10 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP376_0, block10]

theorem stepP376_1 :
    Ripemd160.compressBlock HIn16 (Padding.paddedMessage inputP376) 64 =
      HOut16 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP376_1, block16]

theorem stepP376_2 :
    Ripemd160.compressBlock HIn18 (Padding.paddedMessage inputP376) 128 =
      HOut18 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP376_2, block18]

theorem stepP376_3 :
    Ripemd160.compressBlock HIn19 (Padding.paddedMessage inputP376) 192 =
      HOut19 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP376_3, block19]

theorem stepP376_4 :
    Ripemd160.compressBlock HIn21 (Padding.paddedMessage inputP376) 256 =
      HOut21 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP376_4, block21]

theorem stepP376_5 :
    Ripemd160.compressBlock HIn22 (Padding.paddedMessage inputP376) 320 =
      HOut22 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP376_5, block22]

theorem stepP376_6 :
    Ripemd160.compressBlock HIn23 (Padding.paddedMessage inputP376) 384 =
      HOut23 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP376_6, block23]

theorem spec_P376 : spec inputP376 = expectedP376 := by
  apply spec_of_steps inputP376 expectedP376 statesP376 7
  · decide
  · rfl
  · intro i hi
    interval_cases i <;> first
      | exact stepP376_0
      | exact stepP376_1
      | exact stepP376_2
      | exact stepP376_3
      | exact stepP376_4
      | exact stepP376_5
      | exact stepP376_6
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo

