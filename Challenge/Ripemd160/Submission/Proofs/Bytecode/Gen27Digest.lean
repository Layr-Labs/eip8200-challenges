import Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27InputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Spec

/-!
# `spec 0x916393` equals the stored digest

Proved against the challenge specification, not assumed: the single padded block
is computed, compressed from `H0`, and emitted.

This module is a direct analogue of `AbcDigest.lean` (the `abc` arm), retargeted
at the generated vector #27 literal `0x91 0x63 0x93`.
-/

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27Digest

open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open Gen27InputData

/-- Compressing the single `0x916393` block from the IV yields the final state. -/
theorem stepFinal :
    CompressionCorrect.normalizedCompress Ripemd160.H0 gen27Block = gen27FinalState := by
  decide

/-- The padded `0x916393` message schedules to `gen27Block`. -/
theorem schedule0 :
    CompressionCorrect.schedule (Padding.paddedMessage gen27Input) 0 = gen27Block := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    gen27Input, gen27Block, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide

theorem hashAfter :
    SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage gen27Input) 0 1
      = gen27FinalState := by
  change Ripemd160.compressBlock Ripemd160.H0 (Padding.paddedMessage gen27Input) 0
    = gen27FinalState
  simp only [CompressionCorrect.compressBlock_eq_normalized, schedule0, stepFinal]

theorem emit : SpecBridge.emitDigest gen27FinalState = gen27Digest := by
  unfold SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

theorem hash_gen27 : Ripemd160.hash gen27Input = gen27Digest := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  change SpecBridge.emitDigest
    (SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage gen27Input) 0 1)
      = gen27Digest
  rw [hashAfter, emit]

/-- The obligation the fast path needs: the stored 32-byte answer **is**
`spec 0x916393`. -/
theorem spec_gen27 : Challenge.Ripemd160.spec gen27Input = gen27PaddedDigest := by
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [hash_gen27]
  decide

#print axioms spec_gen27

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Gen27Digest
