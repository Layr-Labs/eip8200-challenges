import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedCompressionBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockMath

open EvmSemantics EvmSemantics.EVM
open PairedLaneUInt256Bridge
open PairedLaneCryptoBridge (CryptoLane)

def packedWord (lo hi : UInt32) : UInt256 :=
  word (PairedLaneCore.pack lo.toBitVec hi.toBitVec)

theorem projection_bits (value : UInt256) :
    (Challenge.EvmProof.Word.toUInt32 value).toBitVec = (bits value).setWidth 32 := by
  rfl

theorem packed_low (lo hi : UInt32) :
    Challenge.EvmProof.Word.toUInt32 (packedWord lo hi) = lo := by
  apply UInt32.eq_of_toBitVec_eq
  rw [projection_bits, packedWord, bits_word,
    BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 256)]
  exact PairedLaneCore.low_pack lo.toBitVec hi.toBitVec

theorem packed_high (lo hi : UInt32) :
    Challenge.EvmProof.Word.toUInt32
      (UInt256.shiftRight (packedWord lo hi) (UInt256.ofNat 128)) = hi := by
  apply UInt32.eq_of_toBitVec_eq
  rw [projection_bits, bits_shr _ 128 (by decide), packedWord, bits_word,
    BitVec.setWidth_ushiftRight_eq_extractLsb]
  exact PairedLaneCore.high_pack lo.toBitVec hi.toBitVec

theorem packed_eq_or (lo hi : UInt32) :
    packedWord lo hi = UInt256.lor
      (UInt256.shiftLeft (Challenge.EvmProof.Word.ofUInt32 hi) (UInt256.ofNat 128))
      (Challenge.EvmProof.Word.ofUInt32 lo) := by
  have hb (x : UInt32) : bits (UInt256.ofNat x.toNat) = x.toBitVec.setWidth 256 := by
    apply BitVec.eq_of_toNat_eq
    simp only [bits_ofNat, BitVec.toNat_ofNat, BitVec.toNat_setWidth, UInt32.toNat_toBitVec]
  apply bits_injective
  rw [packedWord, bits_word, PairedLaneCore.pack, bits_lor,
    bits_shl _ 128 (by decide)]
  change _ = (bits (UInt256.ofNat hi.toNat) <<< 128) ||| bits (UInt256.ofNat lo.toNat)
  rw [hb hi, hb lo]
  have h := BitVec.setWidth_append_eq_shiftLeft_setWidth_or
    (b := hi.toBitVec.setWidth 128) (b' := lo.toBitVec.setWidth 128) (w'' := 256)
  simpa only [BitVec.setWidth_eq,
    BitVec.setWidth_setWidth (by decide : ¬ (128 < 32 ∧ 128 < 256))] using h

theorem startup_packedHash (memory : ByteArray) (address : Nat) :
    PairedStartupTrace.packedHash memory address =
      packedWord (Challenge.EvmProof.Word.toUInt32 (MachineState.readWord memory address))
        (Challenge.EvmProof.Word.toUInt32 (MachineState.readWord memory address)) := by
  unfold PairedStartupTrace.packedHash
  rw [Word.land_comm]
  change UInt256.lor
      (UInt256.shiftLeft (Challenge.EvmProof.Word.mask32 (MachineState.readWord memory address))
        (UInt256.ofNat 128))
      (Challenge.EvmProof.Word.mask32 (MachineState.readWord memory address)) = _
  rw [Challenge.EvmProof.Word.mask32_eq_ofUInt32]
  exact (packed_eq_or _ _).symm

def hashWords (memory : ByteArray) : Compression.EvmHashState :=
  ⟨MachineState.readWord memory 32, MachineState.readWord memory 64,
    MachineState.readWord memory 96, MachineState.readWord memory 128,
    MachineState.readWord memory 160⟩

def readLane (memory : ByteArray) : CryptoLane :=
  ⟨Challenge.EvmProof.Word.toUInt32 (MachineState.readWord memory 32),
    Challenge.EvmProof.Word.toUInt32 (MachineState.readWord memory 64),
    Challenge.EvmProof.Word.toUInt32 (MachineState.readWord memory 96),
    Challenge.EvmProof.Word.toUInt32 (MachineState.readWord memory 128),
    Challenge.EvmProof.Word.toUInt32 (MachineState.readWord memory 160)⟩

theorem readLane_of_hash (memory : ByteArray) (h : Compression.HashState)
    (hh : hashWords memory = Compression.embedHash h) :
    readLane memory = PairedCompressionBridge.ofWorking (CompressionCorrect.workingOfHash h) := by
  have h0 := congrArg Compression.EvmHashState.h0 hh
  have h1 := congrArg Compression.EvmHashState.h1 hh
  have h2 := congrArg Compression.EvmHashState.h2 hh
  have h3 := congrArg Compression.EvmHashState.h3 hh
  have h4 := congrArg Compression.EvmHashState.h4 hh
  change MachineState.readWord memory 32 = Challenge.EvmProof.Word.ofUInt32 h.h0 at h0
  change MachineState.readWord memory 64 = Challenge.EvmProof.Word.ofUInt32 h.h1 at h1
  change MachineState.readWord memory 96 = Challenge.EvmProof.Word.ofUInt32 h.h2 at h2
  change MachineState.readWord memory 128 = Challenge.EvmProof.Word.ofUInt32 h.h3 at h3
  change MachineState.readWord memory 160 = Challenge.EvmProof.Word.ofUInt32 h.h4 at h4
  simp only [readLane, h0, h1, h2, h3, h4, Challenge.EvmProof.Word.toUInt32_ofUInt32,
    PairedCompressionBridge.ofWorking, CompressionCorrect.workingOfHash]

def tailFrame (left right : CryptoLane) : PairedTailTrace.Frame :=
  { a := packedWord left.a right.a
    b := packedWord left.b right.b
    c := packedWord left.c right.c
    d := packedWord left.d right.d
    e := packedWord left.e right.e
    unused3 := PairedStartupTrace.upperWord
    unused5 := PairedStartupTrace.factorWord
    unused6 := PairedStartupTrace.pairWord
    lower := PairedStartupTrace.lowerWord }

theorem combine_packed (memory : ByteArray) (address : Nat) (old a b c d : UInt32)
    (hh : MachineState.readWord memory address = Challenge.EvmProof.Word.ofUInt32 old) :
    PairedTailTrace.combine memory address PairedStartupTrace.lowerWord
      (packedWord a b) (packedWord c d) = Challenge.EvmProof.Word.ofUInt32 (old + (d + a)) := by
  rw [PairedTailTrace.tail_combine_normalized, hh,
    Challenge.EvmProof.Word.toUInt32_ofUInt32, packed_high, packed_low]

theorem tail_hash (memory : ByteArray) (h : Compression.HashState) (left right : CryptoLane)
    (hh : hashWords memory = Compression.embedHash h) :
    hashWords (PairedTailTrace.resultMemory memory (tailFrame left right)) =
      Compression.embedHash (PairedCompressionBridge.combineLanes h left right) := by
  have h0 := congrArg Compression.EvmHashState.h0 hh
  have h1 := congrArg Compression.EvmHashState.h1 hh
  have h2 := congrArg Compression.EvmHashState.h2 hh
  have h3 := congrArg Compression.EvmHashState.h3 hh
  have h4 := congrArg Compression.EvmHashState.h4 hh
  have reads := PairedTailTrace.tail_read_results memory (tailFrame left right)
  simp only [hashWords]
  rw [reads.1, reads.2.1, reads.2.2.1, reads.2.2.2.1, reads.2.2.2.2]
  simp only [PairedTailTrace.result0, PairedTailTrace.result1, PairedTailTrace.result2,
    PairedTailTrace.result3, PairedTailTrace.result4, tailFrame]
  rw [combine_packed memory 64 h.h1 _ _ _ _ h1,
    combine_packed memory 96 h.h2 _ _ _ _ h2,
    combine_packed memory 128 h.h3 _ _ _ _ h3,
    combine_packed memory 160 h.h4 _ _ _ _ h4,
    combine_packed memory 32 h.h0 _ _ _ _ h0]
  rfl

#print axioms projection_bits
#print axioms packed_low
#print axioms packed_high
#print axioms packed_eq_or
#print axioms startup_packedHash
#print axioms readLane_of_hash
#print axioms combine_packed
#print axioms tail_hash

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockMath
