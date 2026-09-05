import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleP64
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock10
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock11

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

def statesP64 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn10
  | 1 => HOut10
  | _ => HOut11

theorem stepP64_0 :
    Ripemd160.compressBlock HIn10 (Padding.paddedMessage inputP64) 0 =
      HOut10 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP64_0, block10]

theorem stepP64_1 :
    Ripemd160.compressBlock HIn11 (Padding.paddedMessage inputP64) 64 =
      HOut11 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP64_1, block11]

theorem spec_P64 : spec inputP64 = expectedP64 := by
  apply spec_of_steps inputP64 expectedP64 statesP64 2
  · decide
  · rfl
  · intro i hi
    interval_cases i <;> first
      | exact stepP64_0
      | exact stepP64_1
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo

