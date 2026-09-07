import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestResult
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Ripemd160
open PatternedInputData PatternedDigest

private theorem targetDigest_eq_literal : targetDigest = ByteArray.mk #[
    0x86, 0x3c, 0x59, 0x85, 0x88, 0xbd, 0x72, 0xa4, 0xba, 0xbf,
    0x36, 0xc6, 0xbb, 0x01, 0xf2, 0x7b, 0xbd, 0xc0, 0xec, 0xd4
  ] := by
  unfold targetDigest
  unfold SpecBridge.emitDigest Crypto.Ripemd160.writeLE32
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

@[simp] theorem targetDigest_size : targetDigest.size = 20 := by
  rw [targetDigest_eq_literal]
  decide

@[simp] theorem paddedDigest_size : paddedDigest.size = 32 := by decide

theorem patternedHash_eq :
    Crypto.Ripemd160.hash patternedInput = targetDigest := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  change SpecBridge.emitDigest
    (SpecBridge.absorbBlocks Crypto.Ripemd160.H0
      (Padding.paddedMessage patternedInput) 0 16) = targetDigest
  rw [PatternedDigestResult.hashAfter_patterned 16 (by decide)]
  change SpecBridge.emitDigest (knownAt 16) = SpecBridge.emitDigest H16
  rfl

theorem spec_patternedInput_eq : spec patternedInput = paddedDigest := by
  unfold spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [patternedHash_eq, targetDigest_eq_literal]
  decide

theorem wordBytes_eq_paddedDigest :
    Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32 = paddedDigest := by
  rw [Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
