import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SpecBridge

set_option warningAsError true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false

/-!
# Concrete RIPEMD-160 certificate for hook word 1

Copied from the fixed-input script in `Hook32Spec` so this module owns the
`decide` of `normalizedCompress` and can be built as its own process.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32DigestHash1
open EvmSemantics EvmSemantics.Crypto
open Challenge.Ripemd160.Submission.Proofs.Bytecode

def literal : ByteArray := ByteArray.mk #[
        0x94, 0xcf, 0x1a, 0xe9, 0x79, 0x77, 0x7b, 0xb0, 0xe2, 0x63, 0x75, 0x25, 0xe8, 0xcc, 0xa0, 0x4e, 0x99, 0x57, 0xbd, 0x78, 0x6a, 0x07, 0x7e, 0xfc, 0x26, 0x3f, 0x33, 0x36, 0xe7, 0x4a, 0xd0, 0x5d]

@[simp] theorem literal_size : literal.size = 32 := by decide

def block : Array UInt32 := #[0xe91acf94, 0xb07b7779, 0x257563e2, 0x4ea0cce8, 0x78bd5799, 0xfc7e076a, 0x36333f26, 0x5dd04ae7, 0x00000080, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000100, 0x00000000]
def state0 : Array UInt32 := #[0xe2b2db39, 0x2ea99cb8, 0xaa4d0391, 0x6329dec3, 0xf6b8d793]
def targetDigest : ByteArray := ByteArray.mk #[0x39, 0xdb, 0xb2, 0xe2, 0xb8, 0x9c, 0xa9, 0x2e, 0x91, 0x03, 0x4d, 0xaa, 0xc3, 0xde, 0x29, 0x63, 0x93, 0xd7, 0xb8, 0xf6]
def paddedDigest : ByteArray := ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x39, 0xdb, 0xb2, 0xe2, 0xb8, 0x9c, 0xa9, 0x2e, 0x91, 0x03, 0x4d, 0xaa, 0xc3, 0xde, 0x29, 0x63, 0x93, 0xd7, 0xb8, 0xf6]
def blockBytes : ByteArray := ByteArray.mk #[0x94, 0xcf, 0x1a, 0xe9, 0x79, 0x77, 0x7b, 0xb0, 0xe2, 0x63, 0x75, 0x25, 0xe8, 0xcc, 0xa0, 0x4e, 0x99, 0x57, 0xbd, 0x78, 0x6a, 0x07, 0x7e, 0xfc, 0x26, 0x3f, 0x33, 0x36, 0xe7, 0x4a, 0xd0, 0x5d, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

@[simp] theorem blockBytes_size : blockBytes.size = 64 := by decide

private theorem lengthBytes_eq :
    Padding.lengthBytes literal = ByteArray.mk #[0, 1, 0, 0, 0, 0, 0, 0] := by
  apply ByteArray.ext_getElem
  · rw [Padding.lengthBytes_size]; decide
  · intro i hleft _hright
    have hi : i < 8 := by simpa only [Padding.lengthBytes_size] using hleft
    rw [Padding.lengthByte literal i hi, literal_size]
    interval_cases i <;>
      norm_num [ByteArray.getElem_eq_getElem_data, ByteArray.size] <;>
      decide

theorem paddedMessage_eq : Padding.paddedMessage literal = blockBytes := by
  unfold Padding.paddedMessage
  rw [literal_size, lengthBytes_eq]
  decide

theorem readBlock (i : Nat) (hi : i < 16) :
    Ripemd160.readLE32 blockBytes (i * 4) = block[i]! := by
  interval_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [blockBytes, block, Ripemd160.readLE32,
        List.range', List.foldl, ByteArray.size,
        ByteArray.getElem_eq_getElem_data] <;>
    try (apply UInt32.eq_of_toBitVec_eq; decide)

theorem schedule0 : CompressionCorrect.schedule blockBytes 0 = block := by
  unfold CompressionCorrect.schedule
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure, List.range', List.foldl]
  rw [show Ripemd160.readLE32 blockBytes (0 * 4) = block[0]! from readBlock 0 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (1 * 4) = block[1]! from readBlock 1 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (2 * 4) = block[2]! from readBlock 2 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (3 * 4) = block[3]! from readBlock 3 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (4 * 4) = block[4]! from readBlock 4 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (5 * 4) = block[5]! from readBlock 5 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (6 * 4) = block[6]! from readBlock 6 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (7 * 4) = block[7]! from readBlock 7 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (8 * 4) = block[8]! from readBlock 8 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (9 * 4) = block[9]! from readBlock 9 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (10 * 4) = block[10]! from readBlock 10 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (11 * 4) = block[11]! from readBlock 11 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (12 * 4) = block[12]! from readBlock 12 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (13 * 4) = block[13]! from readBlock 13 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (14 * 4) = block[14]! from readBlock 14 (by omega)]
  rw [show Ripemd160.readLE32 blockBytes (15 * 4) = block[15]! from readBlock 15 (by omega)]
  decide

theorem step0 : CompressionCorrect.normalizedCompress Ripemd160.H0 block = state0 := by
  decide

theorem hashAfter_block0 :
    SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage literal) 0 1 = state0 := by
  rw [SpecBridge.absorbBlocks_succ, SpecBridge.absorbBlocks_zero]
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [paddedMessage_eq, CompressionCorrect.compressBlock_eq_normalized, schedule0, step0]

theorem emit_state0 : SpecBridge.emitDigest state0 = targetDigest := by
  unfold SpecBridge.emitDigest Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

theorem hash_literal : Ripemd160.hash literal = targetDigest := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  unfold SpecBridge.paddedHash
  rw [literal_size]
  change SpecBridge.emitDigest
      (SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage literal) 0 1)
      = targetDigest
  rw [hashAfter_block0, emit_state0]

theorem spec_literal : Challenge.Ripemd160.spec literal = paddedDigest := by
  unfold Challenge.Ripemd160.spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [hash_literal]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Hook32DigestHash1
