import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentSerialize
import Challenge.Ripemd160.Spec
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentSerialize
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof

private theorem packedHash_eq_pack5 (h : Compression.HashState) :
    StaggerPersistentOutput.packedHash h = PackedOutputMath.pack5 h.h0 h.h1 h.h2 h.h3 h.h4 := by
  simp only [StaggerPersistentOutput.packedHash, PackedOutputMath.pack5, PackedOutputMath.append32,
    Word.lor_comm]

private theorem packed_stage_eq_template (value : UInt256) (shift : Nat) (mask : UInt256) :
    UInt256.lor (UInt256.land (DenseScheduleMemory.DensePacked.shr value shift) mask)
      (DenseScheduleMemory.DensePacked.shl (UInt256.land value mask) shift) =
        DenseScheduleTemplate.packedStage value shift mask := by
  unfold DenseScheduleMemory.DensePacked.shr DenseScheduleMemory.DensePacked.shl
    DenseScheduleTemplate.packedStage
  exact Word.lor_comm _ _

private theorem packed_eq_template (value : UInt256) :
    DenseScheduleMemory.DensePacked.packed value = DenseScheduleTemplate.packedWord value := by
  have hm8 : DenseScheduleMemory.DensePacked.mask8 = DenseScheduleTemplate.mask8 := rfl
  have hm16 : DenseScheduleMemory.DensePacked.mask16 = DenseScheduleTemplate.mask16 := rfl
  unfold DenseScheduleMemory.DensePacked.packed
  rw [hm8, hm16, packed_stage_eq_template, packed_stage_eq_template]
  rfl

theorem bytes_eq_digest (h : Compression.HashState) :
    Data.Bytes.natToBytesPadded (value h).toNat 32 =
      ByteArray.mk (Array.replicate 12 0) ++ SpecBridge.emitDigest (CompressionCorrect.hashArray h) := by
  rw [value, packedHash_eq_pack5, ← packed_eq_template]
  exact PackedOutputMath.packedOutput_eq_prefix_emitDigest h.h0 h.h1 h.h2 h.h3 h.h4

private theorem spec_eq (input : ByteArray) :
    spec input = ByteArray.mk (Array.replicate 12 0) ++ Crypto.Ripemd160.hash input := by
  unfold spec
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  norm_num [List.range', List.range.loop]
  simp [ByteArray.empty, ByteArray.emptyWithCapacity, ByteArray.push]
  decide

theorem bytes_eq_spec (input : ByteArray) :
    Data.Bytes.natToBytesPadded (value (StackRunBridge.hashStateAfter input
      (DriverTrace.blockCount input))).toNat 32 = spec input := by
  rw [bytes_eq_digest, StackRunBridge.hashArray_hashStateAfter, spec_eq,
    ← HashSpecBridge.paddedHash_eq_hash input]
  rfl

theorem returned_spec (s : State) (input : ByteArray) (off limit : UInt256)
    (rho : List UInt256) :
    (result s (StackRunBridge.hashStateAfter input (DriverTrace.blockCount input)) off limit rho).hReturn = spec input := by
  rw [result, StaggerPersistentReturn.returned_bytes]
  exact bytes_eq_spec input
theorem returned_spec_of_hashArray (s : State) (input : ByteArray) (off limit : UInt256)
    (rho : List UInt256) (h : Compression.HashState)
    (hh : CompressionCorrect.hashArray h =
      CompressionSeamBridge.hashAfter input (DriverTrace.blockCount input)) :
    (result s h off limit rho).hReturn = spec input := by
  rw [result, StaggerPersistentReturn.returned_bytes, bytes_eq_digest, hh, spec_eq,
    ← HashSpecBridge.paddedHash_eq_hash input]
  rfl
#print axioms returned_spec_of_hashArray
#print axioms returned_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentSerialize
