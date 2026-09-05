import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleP65
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock10
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock12

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

def statesP65 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn10
  | 1 => HOut10
  | _ => HOut12

theorem stepP65_0 :
    Ripemd160.compressBlock HIn10 (Padding.paddedMessage inputP65) 0 =
      HOut10 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP65_0, block10]

theorem stepP65_1 :
    Ripemd160.compressBlock HIn12 (Padding.paddedMessage inputP65) 64 =
      HOut12 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP65_1, block12]

theorem spec_P65 : spec inputP65 = expectedP65 := by
  apply spec_of_steps inputP65 expectedP65 statesP65 2
  · decide
  · rfl
  · intro i hi
    interval_cases i <;> first
      | exact stepP65_0
      | exact stepP65_1
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo

