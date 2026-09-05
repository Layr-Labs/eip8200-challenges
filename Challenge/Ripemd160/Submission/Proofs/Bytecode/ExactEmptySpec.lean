import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# Result certificate for the empty-calldata dispatch

The twenty-byte digest is the published RIPEMD-160 hash of the empty
string.  The theorem is checked against the challenge specification
through the existing empty-block compression certificate.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactEmptySpec

open Challenge.Ripemd160
open EvmSemantics
open EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode

def emptyDigest : ByteArray := ByteArray.mk #[
  0x9c, 0x11, 0x85, 0xa5, 0xc5, 0xe9, 0xfc, 0x54, 0x61, 0x28,
  0x08, 0x97, 0x7e, 0xe8, 0xf5, 0x48, 0xb2, 0x25, 0x8d, 0x31
]

def paddedDigest : ByteArray := ByteArray.mk #[
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x9c, 0x11, 0x85, 0xa5, 0xc5, 0xe9, 0xfc, 0x54, 0x61, 0x28,
  0x08, 0x97, 0x7e, 0xe8, 0xf5, 0x48, 0xb2, 0x25, 0x8d, 0x31
]

def paddedDigestWord : UInt256 :=
  0x0000000000000000000000009c1185a5c5e9fc54612808977ee8f548b2258d31

@[simp] theorem emptyDigest_size : emptyDigest.size = 20 := by decide

@[simp] theorem paddedDigest_size : paddedDigest.size = 32 := by decide

private theorem paddedLength_empty : Padding.paddedLength 0 / 64 = 1 := by
  decide

private theorem absorb_empty :
    SpecBridge.absorbBlocks Crypto.Ripemd160.H0
        (Padding.paddedMessage ByteArray.empty) 0 1 =
      #[0xa585119c, 0x54fce9c5, 0x97082861, 0x48f5e87e, 0x318d25b2] := by
  rw [show (1 : Nat) = 0 + 1 from rfl, SpecBridge.absorbBlocks_succ,
    SpecBridge.absorbBlocks_zero]
  exact FastEmptyBlock.compress_empty

private theorem emit_empty :
    SpecBridge.emitDigest
        #[0xa585119c, 0x54fce9c5, 0x97082861, 0x48f5e87e, 0x318d25b2] =
      emptyDigest := by
  decide

theorem hash_empty : Crypto.Ripemd160.hash ByteArray.empty = emptyDigest := by
  rw [← HashSpecBridge.paddedHash_eq_hash]
  unfold SpecBridge.paddedHash
  rw [paddedLength_empty, absorb_empty, emit_empty]

theorem spec_empty : spec ByteArray.empty = paddedDigest := by
  unfold spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  rw [hash_empty]
  decide

theorem wordBytes_eq_paddedDigest :
    Data.Bytes.natToBytesPadded paddedDigestWord.toNat 32 = paddedDigest := by
  rw [Challenge.EvmProof.Memory.natToBytesPadded_eq_natToBE]
  decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactEmptySpec
