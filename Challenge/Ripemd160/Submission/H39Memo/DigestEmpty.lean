import Challenge.Ripemd160.Submission.H39Memo.DigestPadding
import Challenge.Ripemd160.Submission.H39Memo.DigestBlock0

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode

theorem scheduleEmpty :
    CompressionCorrect.schedule (Padding.paddedMessage inputEmpty) 0 = B0 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem spec_Empty : spec inputEmpty = expectedEmpty := by
  apply spec_of_steps inputEmpty expectedEmpty (fun i => if i = 0 then HIn0 else HOut0) 1
  · decide
  · rfl
  · intro i hi
    have heq : i = 0 := by omega
    subst i
    change Ripemd160.compressBlock HIn0 (Padding.paddedMessage inputEmpty) 0 = HOut0
    rw [CompressionCorrect.compressBlock_eq_normalized, scheduleEmpty, block0]
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo
