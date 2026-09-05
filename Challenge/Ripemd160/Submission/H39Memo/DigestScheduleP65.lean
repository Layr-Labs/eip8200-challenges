import Challenge.Ripemd160.Submission.H39Memo.DigestPadding

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open Proofs.Bytecode

theorem scheduleP65_0 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP65) 0 = B10 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP65_1 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP65) 64 = B12 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

end Challenge.Ripemd160.Submission.H39Memo
