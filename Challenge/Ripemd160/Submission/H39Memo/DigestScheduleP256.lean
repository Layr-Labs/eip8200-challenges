import Challenge.Ripemd160.Submission.H39Memo.DigestPadding

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open Proofs.Bytecode

theorem scheduleP256_0 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP256) 0 = B10 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP256_1 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP256) 64 = B16 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP256_2 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP256) 128 = B18 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP256_3 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP256) 192 = B19 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP256_4 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP256) 256 = B20 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

end Challenge.Ripemd160.Submission.H39Memo
