import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Generated32Data
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-! Kernel-checked one-block RIPEMD-160 certificate for the guarded vector. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Generated32Spec

open Challenge.Ripemd160 EvmSemantics EvmSemantics.Crypto
open Generated32Data

def finalBlock : ByteArray := ByteArray.mk #[
  0xb5, 0xc1, 0x56, 0xbb, 0xe6, 0x98, 0x8d, 0xf1,
  0x38, 0xe6, 0xaa, 0xce, 0xe6, 0x74, 0x5c, 0x19,
  0xd3, 0xb8, 0x49, 0x29, 0x74, 0x53, 0x33, 0xfe,
  0x64, 0x1b, 0xde, 0x12, 0xe0, 0x0d, 0xcb, 0x78,
  0x80, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,
  0x00, 0x01, 0, 0, 0, 0, 0, 0]

def finalWords : Array UInt32 := #[
  0xbb56c1b5, 0xf18d98e6, 0xceaae638, 0x195c74e6,
  0x2949b8d3, 0xfe335374, 0x12de1b64, 0x78cb0de0,
  0x00000080, 0, 0, 0, 0, 0, 0x00000100, 0]

def H1 : Array UInt32 := #[
  0x32caeffd, 0xfcc7dac2, 0xf13ec9bb, 0xe8f80289, 0xbead0c5b]

private theorem canonicalTail_target :
    HashSpecBridge.canonicalTail targetInput = finalBlock := by
  rw [HashSpecBridge.canonicalTail_eq]
  decide

private theorem schedule_final :
    CompressionCorrect.schedule finalBlock 0 = finalWords := by
  decide

private theorem compress_final :
    Ripemd160.compressBlock Ripemd160.H0 finalBlock 0 = H1 := by
  rw [CompressionCorrect.compressBlock_eq_normalized, schedule_final]
  decide

private theorem emit_H1 : SpecBridge.emitDigest H1 = targetDigest := by
  decide

theorem targetHash_eq : Ripemd160.hash targetInput = targetDigest := by
  rw [HashSpecBridge.hash_eq_two_phase, show targetInput.size / 64 = 0 by decide]
  simp only [SpecBridge.absorbBlocks_zero, Nat.zero_mul]
  rw [canonicalTail_target, show finalBlock.size / 64 = 1 by decide,
    SpecBridge.absorbBlocks_succ]
  simp only [SpecBridge.absorbBlocks_zero, Nat.zero_add, Nat.zero_mul]
  rw [compress_final, emit_H1]

theorem spec_targetInput_eq : spec targetInput = paddedDigest := by
  unfold spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [targetHash_eq]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Generated32Spec
