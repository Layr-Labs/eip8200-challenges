import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Exact64Digest
import Challenge.Ripemd160.Spec
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest55
open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode
def data : ByteArray := ByteArray.mk #[0x7, 0x2c, 0x51, 0x76, 0x9b, 0xc0, 0xe5, 0xa, 0x2f, 0x54, 0x79, 0x9e, 0xc3, 0xe8, 0xd, 0x32, 0x57, 0x7c, 0xa1, 0xc6, 0xeb, 0x10, 0x35, 0x5a, 0x7f, 0xa4, 0xc9, 0xee, 0x13, 0x38, 0x5d, 0x82, 0xa7, 0xcc, 0xf1, 0x16, 0x3b, 0x60, 0x85, 0xaa, 0xcf, 0xf4, 0x19, 0x3e, 0x63, 0x88, 0xad, 0xd2, 0xf7, 0x1c, 0x41, 0x66, 0x8b, 0xb0, 0xd5]
def digest : ByteArray := ByteArray.mk #[0x9, 0x6, 0xf7, 0x77, 0x41, 0x5, 0xd3, 0x64, 0x6, 0x50, 0x54, 0x1c, 0x2e, 0x7b, 0xc1, 0x9b, 0xfe, 0x9b, 0x51, 0x49]
def paddedDigest : ByteArray := ByteArray.mk #[0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x9, 0x6, 0xf7, 0x77, 0x41, 0x5, 0xd3, 0x64, 0x6, 0x50, 0x54, 0x1c, 0x2e, 0x7b, 0xc1, 0x9b, 0xfe, 0x9b, 0x51, 0x49]
def paddedDigestWord : UInt256 := 0x0906f7774105d3640650541c2e7bc19bfe9b5149
theorem data_pattern : data = ShortPatternLogic.data55 := by decide
def finalWords : Array UInt32 := #[0x76512c07, 0xae5c09b, 0x9e79542f, 0x320de8c3, 0xc6a17c57, 0x5a3510eb, 0xeec9a47f, 0x825d3813, 0x16f1cca7, 0xaa85603b, 0x3e19f4cf, 0xd2ad8863, 0x66411cf7, 0x80d5b08b, 0x1b8, 0x0]
def finalState : Array UInt32 := #[0x77f70609, 0x64d30541, 0x1c545006, 0x9bc17b2e, 0x49519bfe]
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
theorem spec_pattern : Challenge.Ripemd160.spec ShortPatternLogic.data55 = paddedDigest := by
  rw [← data_pattern]
  exact spec_data
#print axioms spec_pattern
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest55
