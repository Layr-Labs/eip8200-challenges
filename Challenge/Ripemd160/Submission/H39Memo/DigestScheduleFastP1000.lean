import Challenge.Ripemd160.Submission.H39Memo.DigestPadding

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo.FastSchedule

open Proofs.Bytecode EvmSemantics.Crypto

theorem scheduleP1000_0 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 0 = B10 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_1 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 64 = B16 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_2 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 128 = B18 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_3 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 192 = B19 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_4 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 256 = B21 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_5 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 320 = B24 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_6 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 384 = B25 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_7 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 448 = B26 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_8 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 512 = B27 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_9 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 576 = B28 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_10 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 640 = B29 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_11 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 704 = B30 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_12 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 768 = B31 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_13 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 832 = B32 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_14 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 896 = B33 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

theorem scheduleP1000_15 :
    CompressionCorrect.schedule (Padding.paddedMessage inputP1000) 960 = B34 := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

end Challenge.Ripemd160.Submission.H39Memo.FastSchedule

