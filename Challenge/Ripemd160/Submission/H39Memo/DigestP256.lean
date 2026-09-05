import Challenge.Ripemd160.Submission.H39Memo.DigestScheduleP256
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock10
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock16
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock18
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock19
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock20

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

def statesP256 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => HIn10
  | 1 => HOut10
  | 2 => HOut16
  | 3 => HOut18
  | 4 => HOut19
  | _ => HOut20

theorem stepP256_0 :
    Ripemd160.compressBlock HIn10 (Padding.paddedMessage inputP256) 0 =
      HOut10 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP256_0, block10]

theorem stepP256_1 :
    Ripemd160.compressBlock HIn16 (Padding.paddedMessage inputP256) 64 =
      HOut16 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP256_1, block16]

theorem stepP256_2 :
    Ripemd160.compressBlock HIn18 (Padding.paddedMessage inputP256) 128 =
      HOut18 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP256_2, block18]

theorem stepP256_3 :
    Ripemd160.compressBlock HIn19 (Padding.paddedMessage inputP256) 192 =
      HOut19 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP256_3, block19]

theorem stepP256_4 :
    Ripemd160.compressBlock HIn20 (Padding.paddedMessage inputP256) 256 =
      HOut20 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, scheduleP256_4, block20]

theorem spec_P256 : spec inputP256 = expectedP256 := by
  apply spec_of_steps inputP256 expectedP256 statesP256 5
  · decide
  · rfl
  · intro i hi
    interval_cases i <;> first
      | exact stepP256_0
      | exact stepP256_1
      | exact stepP256_2
      | exact stepP256_3
      | exact stepP256_4
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo

