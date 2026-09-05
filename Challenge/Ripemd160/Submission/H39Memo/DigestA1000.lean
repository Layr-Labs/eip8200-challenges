import Challenge.Ripemd160.Submission.H39Memo.DigestPadding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestD

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto Proofs.Bytecode KnownInputDigest

private theorem paddedA1000_split :
    Padding.paddedMessage KnownInputData.targetInput =
      KnownInputData.targetInput ++
        (ByteArray.mk #[0x80] ++ Padding.zeroBytes KnownInputData.targetInput.size ++
          Padding.lengthBytes KnownInputData.targetInput) := by
  unfold Padding.paddedMessage
  simp only [ByteArray.append_assoc]

theorem compressA1000_prefix (h : Array UInt32) (i : Nat) (hi : i < 15) :
    Ripemd160.compressBlock h (Padding.paddedMessage inputA1000) (i * 64) =
      CompressionCorrect.normalizedCompress h allA := by
  change Ripemd160.compressBlock h (Padding.paddedMessage KnownInputData.targetInput)
    (i * 64) = _
  rw [paddedA1000_split, HashSpecBridge.compressBlock_append_left h _ _ _
    (by rw [KnownInputData.targetInput_size]; omega),
    compress_allA h (i * 64) (by omega)]

theorem scheduleA1000_final :
    CompressionCorrect.schedule (Padding.paddedMessage inputA1000) 960 = finalWords := by
  simp only [Padding.paddedMessage, lengthBytes_expand,
    CompressionCorrect.schedule, Ripemd160.readLE32,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  decide

def statesA1000 (i : Nat) : Array UInt32 :=
  match i with
  | 0 => H0
  | 1 => H1
  | 2 => H2
  | 3 => H3
  | 4 => H4
  | 5 => H5
  | 6 => H6
  | 7 => H7
  | 8 => H8
  | 9 => H9
  | 10 => H10
  | 11 => H11
  | 12 => H12
  | 13 => H13
  | 14 => H14
  | 15 => H15
  | _ => H16

theorem spec_A1000 : spec inputA1000 = expectedA1000 := by
  apply spec_of_steps inputA1000 expectedA1000 statesA1000 16
  · decide
  · rfl
  · intro i hi
    interval_cases i
    · change Ripemd160.compressBlock H0 (Padding.paddedMessage inputA1000) 0 = H1
      rw [show 0 = 0 * 64 by decide, compressA1000_prefix _ 0 (by decide),
        KnownDigestA.step1]
    · change Ripemd160.compressBlock H1 (Padding.paddedMessage inputA1000) 64 = H2
      rw [show 64 = 1 * 64 by decide, compressA1000_prefix _ 1 (by decide),
        KnownDigestA.step2]
    · change Ripemd160.compressBlock H2 (Padding.paddedMessage inputA1000) 128 = H3
      rw [show 128 = 2 * 64 by decide, compressA1000_prefix _ 2 (by decide),
        KnownDigestA.step3]
    · change Ripemd160.compressBlock H3 (Padding.paddedMessage inputA1000) 192 = H4
      rw [show 192 = 3 * 64 by decide, compressA1000_prefix _ 3 (by decide),
        KnownDigestA.step4]
    · change Ripemd160.compressBlock H4 (Padding.paddedMessage inputA1000) 256 = H5
      rw [show 256 = 4 * 64 by decide, compressA1000_prefix _ 4 (by decide),
        KnownDigestB.step5]
    · change Ripemd160.compressBlock H5 (Padding.paddedMessage inputA1000) 320 = H6
      rw [show 320 = 5 * 64 by decide, compressA1000_prefix _ 5 (by decide),
        KnownDigestB.step6]
    · change Ripemd160.compressBlock H6 (Padding.paddedMessage inputA1000) 384 = H7
      rw [show 384 = 6 * 64 by decide, compressA1000_prefix _ 6 (by decide),
        KnownDigestB.step7]
    · change Ripemd160.compressBlock H7 (Padding.paddedMessage inputA1000) 448 = H8
      rw [show 448 = 7 * 64 by decide, compressA1000_prefix _ 7 (by decide),
        KnownDigestB.step8]
    · change Ripemd160.compressBlock H8 (Padding.paddedMessage inputA1000) 512 = H9
      rw [show 512 = 8 * 64 by decide, compressA1000_prefix _ 8 (by decide),
        KnownDigestC.step9]
    · change Ripemd160.compressBlock H9 (Padding.paddedMessage inputA1000) 576 = H10
      rw [show 576 = 9 * 64 by decide, compressA1000_prefix _ 9 (by decide),
        KnownDigestC.step10]
    · change Ripemd160.compressBlock H10 (Padding.paddedMessage inputA1000) 640 = H11
      rw [show 640 = 10 * 64 by decide, compressA1000_prefix _ 10 (by decide),
        KnownDigestC.step11]
    · change Ripemd160.compressBlock H11 (Padding.paddedMessage inputA1000) 704 = H12
      rw [show 704 = 11 * 64 by decide, compressA1000_prefix _ 11 (by decide),
        KnownDigestC.step12]
    · change Ripemd160.compressBlock H12 (Padding.paddedMessage inputA1000) 768 = H13
      rw [show 768 = 12 * 64 by decide, compressA1000_prefix _ 12 (by decide),
        KnownDigestD.step13]
    · change Ripemd160.compressBlock H13 (Padding.paddedMessage inputA1000) 832 = H14
      rw [show 832 = 13 * 64 by decide, compressA1000_prefix _ 13 (by decide),
        KnownDigestD.step14]
    · change Ripemd160.compressBlock H14 (Padding.paddedMessage inputA1000) 896 = H15
      rw [show 896 = 14 * 64 by decide, compressA1000_prefix _ 14 (by decide),
        KnownDigestD.step15]
    · change Ripemd160.compressBlock H15 (Padding.paddedMessage inputA1000) 960 = H16
      rw [CompressionCorrect.compressBlock_eq_normalized, scheduleA1000_final, KnownDigestD.step16]
  · simp only [SpecBridge.emitDigest, Ripemd160.writeLE32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

end Challenge.Ripemd160.Submission.H39Memo
