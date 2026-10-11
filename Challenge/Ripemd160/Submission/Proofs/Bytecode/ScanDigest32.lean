import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Exact64Digest
import Challenge.Ripemd160.Spec
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest32
open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode
def data : ByteArray := ByteArray.mk #[0x7, 0x2c, 0x51, 0x76, 0x9b, 0xc0, 0xe5, 0xa, 0x2f, 0x54, 0x79, 0x9e, 0xc3, 0xe8, 0xd, 0x32, 0x57, 0x7c, 0xa1, 0xc6, 0xeb, 0x10, 0x35, 0x5a, 0x7f, 0xa4, 0xc9, 0xee, 0x13, 0x38, 0x5d, 0x82]
def digest : ByteArray := ByteArray.mk #[0x1a, 0xcf, 0x41, 0xb0, 0x9f, 0x87, 0xac, 0xc9, 0x83, 0xc2, 0xa0, 0x43, 0xf5, 0x4, 0x4c, 0x8f, 0x71, 0xc5, 0x2d, 0xbd]
def paddedDigest : ByteArray := ByteArray.mk #[0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1a, 0xcf, 0x41, 0xb0, 0x9f, 0x87, 0xac, 0xc9, 0x83, 0xc2, 0xa0, 0x43, 0xf5, 0x4, 0x4c, 0x8f, 0x71, 0xc5, 0x2d, 0xbd]
def paddedDigestWord : UInt256 := 0x1acf41b09f87acc983c2a043f5044c8f71c52dbd
theorem data_pattern : data = ShortPatternLogic.data32 := by decide
def finalWords : Array UInt32 := #[0x76512c07, 0xae5c09b, 0x9e79542f, 0x320de8c3, 0xc6a17c57, 0x5a3510eb, 0xeec9a47f, 0x825d3813, 0x80, 0x0, 0x0, 0x0, 0x0, 0x0, 0x100, 0x0]
def finalState : Array UInt32 := #[0xb041cf1a, 0xc9ac879f, 0x43a0c283, 0x8f4c04f5, 0xbd2dc571]
theorem stepFinal : CompressionCorrect.normalizedCompress Ripemd160.H0 finalWords = finalState := by decide
theorem schedule0 : CompressionCorrect.schedule (Padding.paddedMessage data) 0 = finalWords := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    data, finalWords, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide
theorem hashAfter : SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data) 0 1 = finalState := by
  change Ripemd160.compressBlock Ripemd160.H0 (Padding.paddedMessage data) 0 = finalState
  simp only [CompressionCorrect.compressBlock_eq_normalized, schedule0, stepFinal]
theorem emit : SpecBridge.emitDigest finalState = digest := by
  unfold SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide
theorem hash_data : Ripemd160.hash data = digest := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  change SpecBridge.emitDigest (SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data) 0 1) = digest
  rw [hashAfter, emit]
theorem spec_data : Challenge.Ripemd160.spec data = paddedDigest := by
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [hash_data]
  decide
theorem spec_pattern : Challenge.Ripemd160.spec ShortPatternLogic.data32 = paddedDigest := by
  rw [← data_pattern]
  exact spec_data
#print axioms spec_pattern
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest32
