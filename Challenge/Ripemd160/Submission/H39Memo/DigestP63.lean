import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleP63
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock8
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock9

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

def statesP63 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn8
  | 1 => HOut8
  | _ => HOut9

theorem stepP63_0 :
    Ripemd160.compressBlock HIn8 (Padding.paddedMessage inputP63) 0 =
      HOut8 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP63_0, block8]

theorem stepP63_1 :
    Ripemd160.compressBlock HIn9 (Padding.paddedMessage inputP63) 64 =
      HOut9 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP63_1, block9]

theorem spec_P63 : spec inputP63 = expectedP63 := by
  apply spec_of_steps inputP63 expectedP63 statesP63 2
  · decide
  · rfl
  · intro i hi
    interval_cases i <;> first
      | exact stepP63_0
      | exact stepP63_1
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo

