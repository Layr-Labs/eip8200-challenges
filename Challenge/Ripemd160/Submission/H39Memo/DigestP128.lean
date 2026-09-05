import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleP128
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock10
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock16
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock17

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

def statesP128 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn10
  | 1 => HOut10
  | 2 => HOut16
  | _ => HOut17

theorem stepP128_0 :
    Ripemd160.compressBlock HIn10 (Padding.paddedMessage inputP128) 0 =
      HOut10 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP128_0, block10]

theorem stepP128_1 :
    Ripemd160.compressBlock HIn16 (Padding.paddedMessage inputP128) 64 =
      HOut16 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP128_1, block16]

theorem stepP128_2 :
    Ripemd160.compressBlock HIn17 (Padding.paddedMessage inputP128) 128 =
      HOut17 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP128_2, block17]

theorem spec_P128 : spec inputP128 = expectedP128 := by
  apply spec_of_steps inputP128 expectedP128 statesP128 3
  · decide
  · rfl
  · intro i hi
    interval_cases i <;> first
      | exact stepP128_0
      | exact stepP128_1
      | exact stepP128_2
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo

