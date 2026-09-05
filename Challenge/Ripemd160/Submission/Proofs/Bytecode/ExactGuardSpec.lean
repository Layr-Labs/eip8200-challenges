import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownDigestResult
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardData

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Result certificate for the exact `1000 a's` guard

The digest below was independently cross-checked with two RIPEMD-160
implementations before being frozen here.  The theorem itself is checked by
Lean against the challenge's pinned executable specification.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Ripemd160
open ExactGuardData

/-- Raw RIPEMD-160 digest of one thousand ASCII `a` bytes. -/
def targetDigest : ByteArray :=
  KnownInputDigest.targetDigest

/-- Ethereum's 32-byte, left-zero-padded precompile result. -/
def paddedDigest : ByteArray := ByteArray.mk #[
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0xaa, 0x69, 0xde, 0xee, 0x9a, 0x89, 0x22, 0xe9, 0x2f, 0x81,
  0x05, 0xe0, 0x07, 0xf7, 0x61, 0x10, 0xf3, 0x81, 0xe9, 0xcf
]

/-- The same padded result as the word stored by an exact fast path. -/
def paddedDigestWord : UInt256 :=
  0x000000000000000000000000aa69deee9a8922e92f8105e007f76110f381e9cf

@[simp] theorem targetDigest_size : targetDigest.size = 20 := by
  unfold targetDigest KnownInputDigest.targetDigest SpecBridge.emitDigest
  norm_num [List.range, List.range', List.foldl, EvmSemantics.Crypto.Ripemd160.writeLE32,
    ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]

@[simp] theorem paddedDigest_size : paddedDigest.size = 32 := by decide

/-- Concrete hash certificate for the guarded public scoring vector. -/
theorem targetHash_eq :
    Crypto.Ripemd160.hash targetInput = targetDigest := by
  exact KnownDigestResult.hash_target

/-- The hardcoded 32-byte payload is exactly the challenge specification. -/
theorem spec_targetInput_eq : spec targetInput = paddedDigest := by
  unfold spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [targetHash_eq]
  norm_num [targetDigest, KnownInputDigest.targetDigest, SpecBridge.emitDigest,
    List.range, List.range', List.foldl, EvmSemantics.Crypto.Ripemd160.writeLE32,
    ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]

/-- Byte-level certificate relating the `PUSH32`/`MSTORE` word to the payload. -/
theorem wordBytes_eq_paddedDigest :
    Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32 = paddedDigest := by
  rw [Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
