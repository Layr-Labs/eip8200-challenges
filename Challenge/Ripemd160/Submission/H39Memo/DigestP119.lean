import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleP119
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock10
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock13

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

def statesP119 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn10
  | 1 => HOut10
  | _ => HOut13

theorem stepP119_0 :
    Ripemd160.compressBlock HIn10 (Padding.paddedMessage inputP119) 0 =
      HOut10 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP119_0, block10]

theorem stepP119_1 :
    Ripemd160.compressBlock HIn13 (Padding.paddedMessage inputP119) 64 =
      HOut13 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP119_1, block13]

theorem spec_P119 : spec inputP119 = expectedP119 := by
  apply spec_of_steps inputP119 expectedP119 statesP119 2
  · decide
  · rfl
  · intro i hi
    interval_cases i <;> first
      | exact stepP119_0
      | exact stepP119_1
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo

