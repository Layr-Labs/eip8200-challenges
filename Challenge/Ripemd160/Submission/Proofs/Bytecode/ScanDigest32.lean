import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestA
import Challenge.Ripemd160.Spec
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest32
open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode
def data : ByteArray := ByteArray.mk #[
  0x07, 0x2c, 0x51, 0x76, 0x9b, 0xc0, 0xe5, 0x0a, 0x2f, 0x54,
  0x79, 0x9e, 0xc3, 0xe8, 0x0d, 0x32, 0x57, 0x7c, 0xa1, 0xc6,
  0xeb, 0x10, 0x35, 0x5a, 0x7f, 0xa4, 0xc9, 0xee, 0x13, 0x38,
  0x5d, 0x82]
def digest : ByteArray := ByteArray.mk #[
  0x1a, 0xcf, 0x41, 0xb0, 0x9f, 0x87, 0xac, 0xc9, 0x83, 0xc2,
  0xa0, 0x43, 0xf5, 0x04, 0x4c, 0x8f, 0x71, 0xc5, 0x2d, 0xbd]
def paddedDigest : ByteArray := ByteArray.mk #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0x1a, 0xcf, 0x41, 0xb0, 0x9f, 0x87, 0xac, 0xc9, 0x83, 0xc2,
  0xa0, 0x43, 0xf5, 0x04, 0x4c, 0x8f, 0x71, 0xc5, 0x2d, 0xbd]
def paddedDigestWord : UInt256 :=
  0x0000000000000000000000001acf41b09f87acc983c2a043f5044c8f71c52dbd
def words32 : Array UInt32 := #[
  0x76512c07, 0x0ae5c09b, 0x9e79542f, 0x320de8c3,
  0xc6a17c57, 0x5a3510eb, 0xeec9a47f, 0x825d3813,
  0x00000080, 0, 0, 0, 0, 0, 0x00000100, 0]
def state32 : Array UInt32 :=
  #[0xb041cf1a, 0xc9ac879f, 0x43a0c283, 0x8f4c04f5, 0xbd2dc571]
theorem data_pattern : data = ShortPatternLogic.data32 := by decide
theorem schedule32 : CompressionCorrect.schedule (Padding.paddedMessage data) 0 = words32 := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    data, words32, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide
theorem step32 :
    CompressionCorrect.normalizedCompress PatternedDigest.H0 words32 = state32 := by
  decide
theorem hash_data : Ripemd160.hash data = digest := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  unfold SpecBridge.paddedHash
  have hlen : Padding.paddedLength data.size / 64 = 1 := by decide
  rw [hlen, show (1 : Nat) = 0 + 1 from rfl, SpecBridge.absorbBlocks_succ,
    SpecBridge.absorbBlocks_zero]
  rw [show (Ripemd160.H0 : Array UInt32) = PatternedDigest.H0 from rfl]
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule32, step32]
  unfold SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push, state32, digest]
  decide
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
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest32
