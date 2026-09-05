import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleP55
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock5

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

def statesP55 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn5
  | _ => HOut5

theorem stepP55_0 :
    Ripemd160.compressBlock HIn5 (Padding.paddedMessage inputP55) 0 =
      HOut5 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP55_0, block5]

theorem spec_P55 : spec inputP55 = expectedP55 := by
  apply spec_of_steps inputP55 expectedP55 statesP55 1
  · decide
  · rfl
  · intro i hi
    interval_cases i
    exact stepP55_0
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo
