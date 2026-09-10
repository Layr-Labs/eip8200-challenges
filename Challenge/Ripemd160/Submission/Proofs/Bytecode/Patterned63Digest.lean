import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestA
import Challenge.Ripemd160.Spec
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned63Digest
open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode

/-! The 63-byte memoised input pads to exactly TWO blocks, like the 56-byte case,
so this follows ShortPatternDigest's two-block template rather than
Patterned128Digest's three-block one. -/

def data63 : ByteArray := ByteArray.mk #[0x7, 0x2c, 0x51, 0x76, 0x9b, 0xc0, 0xe5, 0xa, 0x2f, 0x54, 0x79, 0x9e, 0xc3, 0xe8, 0xd, 0x32, 0x57, 0x7c, 0xa1, 0xc6, 0xeb, 0x10, 0x35, 0x5a, 0x7f, 0xa4, 0xc9, 0xee, 0x13, 0x38, 0x5d, 0x82, 0xa7, 0xcc, 0xf1, 0x16, 0x3b, 0x60, 0x85, 0xaa, 0xcf, 0xf4, 0x19, 0x3e, 0x63, 0x88, 0xad, 0xd2, 0xf7, 0x1c, 0x41, 0x66, 0x8b, 0xb0, 0xd5, 0xfa, 0x1f, 0x44, 0x69, 0x8e, 0xb3, 0xd8, 0xfd]
def words63_0 : Array UInt32 := #[0x76512c07, 0xae5c09b, 0x9e79542f, 0x320de8c3, 0xc6a17c57, 0x5a3510eb, 0xeec9a47f, 0x825d3813, 0x16f1cca7, 0xaa85603b, 0x3e19f4cf, 0xd2ad8863, 0x66411cf7, 0xfad5b08b, 0x8e69441f, 0x80fdd8b3]
def words63_1 : Array UInt32 := #[0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x1f8, 0x0]
def state63_1 : Array UInt32 := #[3677480614, 3462446910, 721677021, 2903686661, 352238910]
def state63_2 : Array UInt32 := #[3842934839, 3760318690, 1186007892, 876035043, 3991344675]

theorem step63_0 : CompressionCorrect.normalizedCompress PatternedDigest.H0 words63_0 = state63_1 := by decide
theorem step63_1 : CompressionCorrect.normalizedCompress state63_1 words63_1 = state63_2 := by decide

theorem data63_pattern : data63 = PatternedInputData.patternedInput.extract 0 63 := by decide

theorem schedule63_0 : CompressionCorrect.schedule (Padding.paddedMessage data63) 0 = words63_0 := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    data63, words63_0, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide

theorem schedule63_1 : CompressionCorrect.schedule (Padding.paddedMessage data63) 64 = words63_1 := by
  unfold CompressionCorrect.schedule Crypto.Ripemd160.readLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.foldl, Padding.paddedMessage, Padding.zeroBytes,
    Padding.zeroCount, Padding.paddedLength, Padding.lengthBytes,
    data63, words63_1, ByteArray.size, ByteArray.getElem_eq_getElem_data]
  decide

theorem hashAfter63 :
    SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data63) 0 2 = state63_2 := by
  change Ripemd160.compressBlock (Ripemd160.compressBlock PatternedDigest.H0
    (Padding.paddedMessage data63) 0) (Padding.paddedMessage data63) 64 = state63_2
  simp only [CompressionCorrect.compressBlock_eq_normalized, schedule63_0, schedule63_1,
    step63_0, step63_1]

def digest63 : ByteArray := ByteArray.mk #[0x37, 0x88, 0xe, 0xe5, 0xe2, 0xe8, 0x21, 0xe0, 0x54, 0xb, 0xb1, 0x46, 0xe3, 0x3b, 0x37, 0x34, 0x23, 0x16, 0xe7, 0xed]

def paddedDigest : ByteArray := ByteArray.mk #[0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x37, 0x88, 0xe, 0xe5, 0xe2, 0xe8, 0x21, 0xe0, 0x54, 0xb, 0xb1, 0x46, 0xe3, 0x3b, 0x37, 0x34, 0x23, 0x16, 0xe7, 0xed]

def paddedDigestWord : UInt256 :=
  0x00000000000000000000000037880ee5e2e821e0540bb146e33b37342316e7ed

@[simp] theorem paddedDigest_size : paddedDigest.size = 32 := by decide

theorem emit63 : SpecBridge.emitDigest state63_2 = digest63 := by
  unfold SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

theorem hash63 : Ripemd160.hash data63 = digest63 := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  change SpecBridge.emitDigest
    (SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage data63) 0 2) = digest63
  rw [hashAfter63, emit63]

/-- `ShortPatternLogic.data63` is `patternedInput.extract 0 63`; `data63` is the
same bytes written out, so the two agree definitionally. -/
theorem data63_eq_logic : data63 = ShortPatternLogic.data63 := by
  rw [data63_pattern]; rfl

theorem spec_data_eq : Challenge.Ripemd160.spec ShortPatternLogic.data63 = paddedDigest := by
  rw [← data63_eq_logic]
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [hash63]
  decide

theorem wordBytes_eq_paddedDigest :
    Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32 = paddedDigest := by
  rw [Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned63Digest
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned63Digest.spec_data_eq
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned63Digest.wordBytes_eq_paddedDigest
