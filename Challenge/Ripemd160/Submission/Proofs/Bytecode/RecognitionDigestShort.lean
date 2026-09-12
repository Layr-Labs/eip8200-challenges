import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestA
import Challenge.Ripemd160.Spec
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigestShort
open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode
def data56 : ByteArray := ByteArray.mk #[0x7, 0x2c, 0x51, 0x76, 0x9b, 0xc0, 0xe5, 0xa, 0x2f, 0x54, 0x79, 0x9e, 0xc3, 0xe8, 0xd, 0x32, 0x57, 0x7c, 0xa1, 0xc6, 0xeb, 0x10, 0x35, 0x5a, 0x7f, 0xa4, 0xc9, 0xee, 0x13, 0x38, 0x5d, 0x82, 0xa7, 0xcc, 0xf1, 0x16, 0x3b, 0x60, 0x85, 0xaa, 0xcf, 0xf4, 0x19, 0x3e, 0x63, 0x88, 0xad, 0xd2, 0xf7, 0x1c, 0x41, 0x66, 0x8b, 0xb0, 0xd5, 0xfa]
def words56_0 : Array UInt32 := #[0x76512c07, 0xae5c09b, 0x9e79542f, 0x320de8c3, 0xc6a17c57, 0x5a3510eb, 0xeec9a47f, 0x825d3813, 0x16f1cca7, 0xaa85603b, 0x3e19f4cf, 0xd2ad8863, 0x66411cf7, 0xfad5b08b, 0x80, 0x0]
def words56_1 : Array UInt32 := #[0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1c0, 0x0]
def data120 : ByteArray := ByteArray.mk #[0x7, 0x2c, 0x51, 0x76, 0x9b, 0xc0, 0xe5, 0xa, 0x2f, 0x54, 0x79, 0x9e, 0xc3, 0xe8, 0xd, 0x32, 0x57, 0x7c, 0xa1, 0xc6, 0xeb, 0x10, 0x35, 0x5a, 0x7f, 0xa4, 0xc9, 0xee, 0x13, 0x38, 0x5d, 0x82, 0xa7, 0xcc, 0xf1, 0x16, 0x3b, 0x60, 0x85, 0xaa, 0xcf, 0xf4, 0x19, 0x3e, 0x63, 0x88, 0xad, 0xd2, 0xf7, 0x1c, 0x41, 0x66, 0x8b, 0xb0, 0xd5, 0xfa, 0x1f, 0x44, 0x69, 0x8e, 0xb3, 0xd8, 0xfd, 0x22, 0x47, 0x6c, 0x91, 0xb6, 0xdb, 0x0, 0x25, 0x4a, 0x6f, 0x94, 0xb9, 0xde, 0x3, 0x28, 0x4d, 0x72, 0x97, 0xbc, 0xe1, 0x6, 0x2b, 0x50, 0x75, 0x9a, 0xbf, 0xe4, 0x9, 0x2e, 0x53, 0x78, 0x9d, 0xc2, 0xe7, 0xc, 0x31, 0x56, 0x7b, 0xa0, 0xc5, 0xea, 0xf, 0x34, 0x59, 0x7e, 0xa3, 0xc8, 0xed, 0x12, 0x37, 0x5c, 0x81, 0xa6, 0xcb, 0xf0, 0x15, 0x3a]
def words120_0 : Array UInt32 := #[0x76512c07, 0xae5c09b, 0x9e79542f, 0x320de8c3, 0xc6a17c57, 0x5a3510eb, 0xeec9a47f, 0x825d3813, 0x16f1cca7, 0xaa85603b, 0x3e19f4cf, 0xd2ad8863, 0x66411cf7, 0xfad5b08b, 0x8e69441f, 0x22fdd8b3]
def words120_1 : Array UInt32 := #[0xb6916c47, 0x4a2500db, 0xdeb9946f, 0x724d2803, 0x6e1bc97, 0x9a75502b, 0x2e09e4bf, 0xc29d7853, 0x56310ce7, 0xeac5a07b, 0x7e59340f, 0x12edc8a3, 0xa6815c37, 0x3a15f0cb, 0x80, 0x0]
def words120_2 : Array UInt32 := #[0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x3c0, 0x0]
def state56_1 : Array UInt32 := #[1006956832, 905006325, 952596882, 3052582878, 3200013773]
theorem step56_0 : CompressionCorrect.normalizedCompress PatternedDigest.H0 words56_0 = state56_1 := by decide
#print axioms step56_0
def state56_2 : Array UInt32 := #[1273553624, 2247891373, 1605742043, 829834917, 51713230]
def state120_2 : Array UInt32 := #[1809980522, 1134928511, 830608261, 3376621497, 1621946939]
theorem step56_1 : CompressionCorrect.normalizedCompress state56_1 words56_1 = state56_2 := by decide
theorem step120_1 : CompressionCorrect.normalizedCompress PatternedDigest.H1 words120_1 = state120_2 := by decide
theorem data56_pattern : data56 = PatternedInputData.patternedInput.extract 0 56 := by decide
theorem schedule56_0 : CompressionCorrect.schedule (Padding.paddedMessage data56) 0 = words56_0 := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    data56, words56_0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide
theorem schedule56_1 : CompressionCorrect.schedule (Padding.paddedMessage data56) 64 = words56_1 := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    data56, words56_1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide
theorem data120_pattern : data120 = PatternedInputData.patternedInput.extract 0 120 := by decide
theorem schedule120_0 : CompressionCorrect.schedule (Padding.paddedMessage data120) 0 = words120_0 := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    data120, words120_0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide
theorem schedule120_1 : CompressionCorrect.schedule (Padding.paddedMessage data120) 64 = words120_1 := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    data120, words120_1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide
theorem schedule120_2 : CompressionCorrect.schedule (Padding.paddedMessage data120) 128 = words120_2 := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    data120, words120_2, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide


def state120_3 : Array UInt32 := #[1795940941, 1152365087, 247754787, 3389695315, 3166900022]
theorem step120_2 : CompressionCorrect.normalizedCompress state120_2 words120_2 = state120_3 := by decide
theorem step120_0 : CompressionCorrect.normalizedCompress PatternedDigest.H0 words120_0 = PatternedDigest.H1 := PatternedDigestA.step0

theorem hashAfter56 : SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data56) 0 2 = state56_2 := by
  change Ripemd160.compressBlock (Ripemd160.compressBlock PatternedDigest.H0 (Padding.paddedMessage data56) 0) (Padding.paddedMessage data56) 64 = state56_2
  simp only [CompressionCorrect.compressBlock_eq_normalized, schedule56_0, schedule56_1, step56_0, step56_1]

theorem hashAfter120 : SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data120) 0 3 = state120_3 := by
  change Ripemd160.compressBlock (Ripemd160.compressBlock (Ripemd160.compressBlock PatternedDigest.H0 (Padding.paddedMessage data120) 0) (Padding.paddedMessage data120) 64) (Padding.paddedMessage data120) 128 = state120_3
  simp only [CompressionCorrect.compressBlock_eq_normalized, schedule120_0, schedule120_1, schedule120_2, step120_0, step120_1, step120_2]

def digest56 : ByteArray := ByteArray.mk #[0xd8, 0xe2, 0xe8, 0x4b, 0xad, 0x19, 0xfc, 0x85, 0xdb, 0xad, 0xb5, 0x5f, 0xa5, 0x46, 0x76, 0x31, 0xce, 0x14, 0x15, 0x3]
def paddedDigest56 : ByteArray := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xd8, 0xe2, 0xe8, 0x4b, 0xad, 0x19, 0xfc, 0x85, 0xdb, 0xad, 0xb5, 0x5f, 0xa5, 0x46, 0x76, 0x31, 0xce, 0x14, 0x15, 0x3]
theorem emit56 : SpecBridge.emitDigest state56_2 = digest56 := by
  unfold SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

theorem hash56 : Ripemd160.hash data56 = digest56 := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  change SpecBridge.emitDigest (SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data56) 0 2) = digest56
  rw [hashAfter56, emit56]

theorem spec56 : Challenge.Ripemd160.spec data56 = paddedDigest56 := by
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [hash56]
  decide
#print axioms spec56

def digest120 : ByteArray := ByteArray.mk #[0x4d, 0xe2, 0xb, 0x6b, 0x1f, 0xb2, 0xaf, 0x44, 0x23, 0x70, 0xc4, 0xe, 0x53, 0xa5, 0xa, 0xca, 0x36, 0xf, 0xc3, 0xbc]
def paddedDigest120 : ByteArray := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x4d, 0xe2, 0xb, 0x6b, 0x1f, 0xb2, 0xaf, 0x44, 0x23, 0x70, 0xc4, 0xe, 0x53, 0xa5, 0xa, 0xca, 0x36, 0xf, 0xc3, 0xbc]
theorem emit120 : SpecBridge.emitDigest state120_3 = digest120 := by
  unfold SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

theorem hash120 : Ripemd160.hash data120 = digest120 := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  change SpecBridge.emitDigest (SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data120) 0 3) = digest120
  rw [hashAfter120, emit120]

theorem spec120 : Challenge.Ripemd160.spec data120 = paddedDigest120 := by
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [hash120]
  decide
#print axioms spec120
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigestShort
