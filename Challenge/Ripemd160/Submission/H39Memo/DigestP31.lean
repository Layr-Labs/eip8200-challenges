import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleP31
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock3

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

def statesP31 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn3
  | _ => HOut3

theorem stepP31_0 :
    Ripemd160.compressBlock HIn3 (Padding.paddedMessage inputP31) 0 =
      HOut3 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP31_0, block3]

theorem spec_P31 : spec inputP31 = expectedP31 := by
  apply spec_of_steps inputP31 expectedP31 statesP31 1
  · decide
  · rfl
  · intro i hi
    interval_cases i
    exact stepP31_0
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo
