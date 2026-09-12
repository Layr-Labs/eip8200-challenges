import Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedInput04Data
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Spec

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedDigest04

open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open GeneratedInput04Data

/-- The one padded block for the 32-byte generated corpus vector. -/
def generatedBlock : Array UInt32 := #[
  0xe91acf94, 0xb07b7779, 0x257563e2, 0x4ea0cce8,
  0x78bd5799, 0xfc7e076a, 0x36333f26, 0x5dd04ae7,
  0x00000080, 0x00000000, 0x00000000, 0x00000000,
  0x00000000, 0x00000000, 0x00000100, 0x00000000]

/-- The chaining state after compressing that block from the RIPEMD-160 IV. -/
def generatedFinalState : Array UInt32 := #[
  0xe2b2db39, 0x2ea99cb8, 0xaa4d0391, 0x6329dec3, 0xf6b8d793]

theorem stepFinal :
    CompressionCorrect.normalizedCompress Ripemd160.H0 generatedBlock =
      generatedFinalState := by
  decide

theorem schedule0 :
    CompressionCorrect.schedule (Padding.paddedMessage generatedInput) 0 =
      generatedBlock := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    GeneratedInput04Data.generatedInput, generatedBlock, ByteArray.size,
    ByteArray.getElem_eq_getElem_data]
  decide

theorem hashAfter :
    SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage generatedInput) 0 1
      = generatedFinalState := by
  change Ripemd160.compressBlock Ripemd160.H0
      (Padding.paddedMessage generatedInput) 0 = generatedFinalState
  simp only [CompressionCorrect.compressBlock_eq_normalized, schedule0, stepFinal]

theorem emit : SpecBridge.emitDigest generatedFinalState = generatedDigest := by
  unfold SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

theorem hash_generated : Ripemd160.hash generatedInput = generatedDigest := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  change SpecBridge.emitDigest
    (SpecBridge.absorbBlocks Ripemd160.H0
      (Padding.paddedMessage generatedInput) 0 1) = generatedDigest
  rw [hashAfter, emit]

theorem spec_generated :
    Challenge.Ripemd160.spec generatedInput = generatedPaddedDigest := by
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [hash_generated]
  decide

theorem wordBytes_eq_paddedDigest :
    Data.Bytes.natToBytesPadded generatedDigestWord.toNat 32 =
      generatedPaddedDigest := by
  rw [Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedDigest04
