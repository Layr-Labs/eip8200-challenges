import Challenge.Ripemd160.Submission.H39Memo.DigestBridge
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock1

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

theorem scheduleAbc :
    CompressionCorrect.schedule (Padding.paddedMessage inputAbc) 0 = B1 := by
  norm_num (config := { maxSteps := 1000000 })
    [CompressionCorrect.schedule, Ripemd160.readLE32,
      Padding.paddedMessage, Padding.zeroBytes, Padding.zeroCount,
      Padding.paddedLength, Padding.lengthBytes, inputAbc,
      List.range', List.foldl, Array.setIfInBounds,
      ByteArray.getElem_eq_getElem_data, ByteArray.data_append]
  decide

theorem spec_Abc : spec inputAbc = expectedAbc := by
  apply spec_of_steps inputAbc expectedAbc (fun i => if i = 0 then HIn1 else HOut1) 1
  · decide
  · rfl
  · intro i hi
    have heq : i = 0 := by omega
    subst i
    change Ripemd160.compressBlock HIn1 (Padding.paddedMessage inputAbc) 0 = HOut1
    rw [CompressionCorrect.compressBlock_eq_normalized, scheduleAbc, block1]
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo
