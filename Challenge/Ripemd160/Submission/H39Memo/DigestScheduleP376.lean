import Challenge.Ripemd160.Submission.H39Memo.DigestPadding

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open Proofs.Bytecode

theorem scheduleP376_0 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP376) 0 = B10 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP376_1 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP376) 64 = B16 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP376_2 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP376) 128 = B18 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP376_3 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP376) 192 = B19 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP376_4 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP376) 256 = B21 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP376_5 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP376) 320 = B22 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP376_6 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP376) 384 = B23 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, EvmSemantics.Crypto.Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

end Challenge.Ripemd160.Submission.H39Memo
