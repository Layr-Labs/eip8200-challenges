import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleP56
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock6
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock7

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

def statesP56 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn6
  | 1 => HOut6
  | _ => HOut7

theorem stepP56_0 :
    Ripemd160.compressBlock HIn6 (Padding.paddedMessage inputP56) 0 =
      HOut6 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP56_0, block6]

theorem stepP56_1 :
    Ripemd160.compressBlock HIn7 (Padding.paddedMessage inputP56) 64 =
      HOut7 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP56_1, block7]

theorem spec_P56 : spec inputP56 = expectedP56 := by
  apply spec_of_steps inputP56 expectedP56 statesP56 2
  · decide
  · rfl
  · intro i hi
    interval_cases i <;> first
      | exact stepP56_0
      | exact stepP56_1
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo

