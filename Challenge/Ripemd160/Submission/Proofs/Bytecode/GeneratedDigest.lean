import Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedInputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Spec

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedDigest

open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open GeneratedInputData

/-- The one padded block for the 32-byte generated corpus vector. -/
def generatedBlock : Array UInt32 := #[
  0x17dedd73, 0x6f69560c, 0x7d41e08b, 0x83e423ea,
  0xc731f65e, 0xfbc9bb60, 0x5a8862e9, 0x42d487ed,
  0x00000080, 0x00000000, 0x00000000, 0x00000000,
  0x00000000, 0x00000000, 0x00000100, 0x00000000]

/-- The chaining state after compressing that block from the RIPEMD-160 IV. -/
def generatedFinalState : Array UInt32 := #[
  0xce326197, 0x96ada6a9, 0x5fa6570a, 0x0bfe0a7f, 0x84013a0e]

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
    GeneratedInputData.generatedInput, generatedBlock, ByteArray.size,
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.GeneratedDigest
