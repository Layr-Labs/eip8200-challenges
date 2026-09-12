import Challenge.Ripemd160.Submission.Proofs.Bytecode.Exact64Digest
import Challenge.Ripemd160.Spec
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest1
open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode
def data : ByteArray := ByteArray.mk #[0x7]
def digest : ByteArray := ByteArray.mk #[0x5b, 0xe9, 0x25, 0x9e, 0x94, 0x78, 0x20, 0x2d, 0xd0, 0xc1, 0xf4, 0xeb, 0xc, 0x4e, 0xd0, 0x44, 0x2d, 0xbe, 0xb2, 0xcd]
def paddedDigest : ByteArray := ByteArray.mk #[0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x5b, 0xe9, 0x25, 0x9e, 0x94, 0x78, 0x20, 0x2d, 0xd0, 0xc1, 0xf4, 0xeb, 0xc, 0x4e, 0xd0, 0x44, 0x2d, 0xbe, 0xb2, 0xcd]
def paddedDigestWord : UInt256 := 0x5be9259e9478202dd0c1f4eb0c4ed0442dbeb2cd
def finalWords : Array UInt32 := #[0x8007, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x8, 0x0]
def finalState : Array UInt32 := #[0x9e25e95b, 0x2d207894, 0xebf4c1d0, 0x44d04e0c, 0xcdb2be2d]
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
#print axioms spec_data
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionDigest1
