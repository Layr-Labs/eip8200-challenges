import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376DigestResult
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376GuardSpec

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Ripemd160
open Patterned376InputData Patterned376Digest

private theorem targetDigest_eq_literal : targetDigest = ByteArray.mk #[
    0xf6, 0xce, 0xa8, 0xd2, 0xa4, 0x91, 0xf5, 0xdc, 0x27, 0x6a,
    0xa1, 0xf7, 0x61, 0x8b, 0x4d, 0x7a, 0x55, 0x2e, 0xc4, 0xad
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

theorem patterned376Hash_eq :
    Crypto.Ripemd160.hash patterned376Input = targetDigest := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  change SpecBridge.emitDigest
    (SpecBridge.absorbBlocks Crypto.Ripemd160.H0
      (Padding.paddedMessage patterned376Input) 0 7) = targetDigest
  rw [Patterned376DigestResult.hashAfter_patterned376 7 (by decide)]
  change SpecBridge.emitDigest (knownAt 7) = SpecBridge.emitDigest H7
  rfl

theorem spec_patterned376Input_eq : spec patterned376Input = paddedDigest := by
  unfold spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [patterned376Hash_eq, targetDigest_eq_literal]
  decide

theorem wordBytes_eq_paddedDigest :
    Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32 = paddedDigest := by
  rw [Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376GuardSpec
