import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestA
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Exact64Digest
import Challenge.Ripemd160.Spec
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest119
open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode
def data : ByteArray := ByteArray.mk #[0x7, 0x2c, 0x51, 0x76, 0x9b, 0xc0, 0xe5, 0xa, 0x2f, 0x54, 0x79, 0x9e, 0xc3, 0xe8, 0xd, 0x32, 0x57, 0x7c, 0xa1, 0xc6, 0xeb, 0x10, 0x35, 0x5a, 0x7f, 0xa4, 0xc9, 0xee, 0x13, 0x38, 0x5d, 0x82, 0xa7, 0xcc, 0xf1, 0x16, 0x3b, 0x60, 0x85, 0xaa, 0xcf, 0xf4, 0x19, 0x3e, 0x63, 0x88, 0xad, 0xd2, 0xf7, 0x1c, 0x41, 0x66, 0x8b, 0xb0, 0xd5, 0xfa, 0x1f, 0x44, 0x69, 0x8e, 0xb3, 0xd8, 0xfd, 0x22, 0x47, 0x6c, 0x91, 0xb6, 0xdb, 0x0, 0x25, 0x4a, 0x6f, 0x94, 0xb9, 0xde, 0x3, 0x28, 0x4d, 0x72, 0x97, 0xbc, 0xe1, 0x6, 0x2b, 0x50, 0x75, 0x9a, 0xbf, 0xe4, 0x9, 0x2e, 0x53, 0x78, 0x9d, 0xc2, 0xe7, 0xc, 0x31, 0x56, 0x7b, 0xa0, 0xc5, 0xea, 0xf, 0x34, 0x59, 0x7e, 0xa3, 0xc8, 0xed, 0x12, 0x37, 0x5c, 0x81, 0xa6, 0xcb, 0xf0, 0x15]
def digest : ByteArray := ByteArray.mk #[0x2b, 0x95, 0x67, 0xd6, 0x84, 0xdc, 0x89, 0xcd, 0x54, 0x62, 0xe, 0x46, 0x2, 0x9f, 0x5b, 0xda, 0xe, 0xca, 0xb7, 0x87]
def paddedDigest : ByteArray := ByteArray.mk #[0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x2b, 0x95, 0x67, 0xd6, 0x84, 0xdc, 0x89, 0xcd, 0x54, 0x62, 0xe, 0x46, 0x2, 0x9f, 0x5b, 0xda, 0xe, 0xca, 0xb7, 0x87]
def paddedDigestWord : UInt256 := 0x2b9567d684dc89cd54620e46029f5bda0ecab787
theorem data_pattern : data = ShortPatternLogic.data119 := by decide
def finalWords : Array UInt32 := #[0xb6916c47, 0x4a2500db, 0xdeb9946f, 0x724d2803, 0x6e1bc97, 0x9a75502b, 0x2e09e4bf, 0xc29d7853, 0x56310ce7, 0xeac5a07b, 0x7e59340f, 0x12edc8a3, 0xa6815c37, 0x8015f0cb, 0x3b8, 0x0]
def finalState : Array UInt32 := #[0xd667952b, 0xcd89dc84, 0x460e6254, 0xda5b9f02, 0x87b7ca0e]
theorem stepFinal : CompressionCorrect.normalizedCompress PatternedDigest.H1 finalWords = finalState := by decide
theorem schedule0 : CompressionCorrect.schedule (Padding.paddedMessage data) 0 = PatternedDigest.block0 := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    data, PatternedDigest.block0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide
theorem schedule64 : CompressionCorrect.schedule (Padding.paddedMessage data) 64 = finalWords := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    data, finalWords, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide
theorem hashAfter : SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data) 0 2 = finalState := by
  change Ripemd160.compressBlock (Ripemd160.compressBlock PatternedDigest.H0 (Padding.paddedMessage data) 0) (Padding.paddedMessage data) 64 = finalState
  simp only [CompressionCorrect.compressBlock_eq_normalized, schedule0, schedule64, PatternedDigestA.step0, stepFinal]
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
  change SpecBridge.emitDigest (SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data) 0 2) = digest
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
theorem spec_pattern : Challenge.Ripemd160.spec ShortPatternLogic.data119 = paddedDigest := by
  rw [← data_pattern]
  exact spec_data
#print axioms spec_pattern
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest119
