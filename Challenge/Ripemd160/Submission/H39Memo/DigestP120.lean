import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleP120
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock10
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock14
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock15

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

def statesP120 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn10
  | 1 => HOut10
  | 2 => HOut14
  | _ => HOut15

theorem stepP120_0 :
    Ripemd160.compressBlock HIn10 (Padding.paddedMessage inputP120) 0 =
      HOut10 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP120_0, block10]

theorem stepP120_1 :
    Ripemd160.compressBlock HIn14 (Padding.paddedMessage inputP120) 64 =
      HOut14 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP120_1, block14]

theorem stepP120_2 :
    Ripemd160.compressBlock HIn15 (Padding.paddedMessage inputP120) 128 =
      HOut15 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP120_2, block15]

theorem spec_P120 : spec inputP120 = expectedP120 := by
  apply spec_of_steps inputP120 expectedP120 statesP120 3
  · decide
  · rfl
  · intro i hi
    interval_cases i <;> first
      | exact stepP120_0
      | exact stepP120_1
      | exact stepP120_2
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo

