import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcInputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Spec

/-!
# `spec "abc"` equals the stored digest

Proved against the challenge specification, not assumed: the single padded block
is computed, compressed from `H0`, and emitted.

This module is a direct analogue of `ScanDigest1.lean` (the size-1 patterned
arm), retargeted at the literal `"abc"`.  The block constants `abcBlock` /
`abcFinalState` agree with `H39Memo/DigestData.lean`'s `B1` / `HOut1` from
submission `cf170158-635a-4916-a3ca-220a0d3a4099` (commit `3dad8ba6`,
co-authored by Amal-David), which proved the same statement as `spec_Abc` by the
equivalent `spec_of_steps` route.
-/

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcDigest

open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open AbcInputData

/-- Compressing the single `"abc"` block from the IV yields the final state. -/
theorem stepFinal :
    CompressionCorrect.normalizedCompress Ripemd160.H0 abcBlock = abcFinalState := by
  decide

/-- The padded `"abc"` message schedules to `abcBlock`. -/
theorem schedule0 :
    CompressionCorrect.schedule (Padding.paddedMessage abcInput) 0 = abcBlock := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    abcInput, abcBlock, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide

theorem hashAfter :
    SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage abcInput) 0 1
      = abcFinalState := by
  change Ripemd160.compressBlock Ripemd160.H0 (Padding.paddedMessage abcInput) 0
    = abcFinalState
  simp only [CompressionCorrect.compressBlock_eq_normalized, schedule0, stepFinal]

theorem emit : SpecBridge.emitDigest abcFinalState = abcDigest := by
  unfold SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

theorem hash_abc : Ripemd160.hash abcInput = abcDigest := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  change SpecBridge.emitDigest
    (SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage abcInput) 0 1)
      = abcDigest
  rw [hashAfter, emit]

/-- The obligation the fast path needs: the stored 32-byte answer **is**
`spec "abc"`. -/
theorem spec_abc : Challenge.Ripemd160.spec abcInput = abcPaddedDigest := by
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [hash_abc]
  decide

#print axioms spec_abc

end Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcDigest
