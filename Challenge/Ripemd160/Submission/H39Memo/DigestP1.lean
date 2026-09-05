import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleP1
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock2

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

def statesP1 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn2
  | _ => HOut2

theorem stepP1_0 :
    Ripemd160.compressBlock HIn2 (Padding.paddedMessage inputP1) 0 =
      HOut2 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP1_0, block2]

theorem spec_P1 : spec inputP1 = expectedP1 := by
  apply spec_of_steps inputP1 expectedP1 statesP1 1
  · decide
  · rfl
  · intro i hi
    interval_cases i
    exact stepP1_0
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo
