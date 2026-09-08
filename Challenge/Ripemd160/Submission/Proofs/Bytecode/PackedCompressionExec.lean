import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFullRounds
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFrameFold
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOperandFold
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedInitialFrame

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionExec
open EvmSemantics PackedStepFrame PackedRoundSequence PackedCompression

/-- The executed frame recurrence has the arithmetic compression result.
Preprocessing and the concrete hash-entry trace still supply these premises. -/
theorem frame_result (memory : ByteArray) (words : Nat → UInt256)
    (values : Nat → UInt32) (hgap : PackedGapInvariant.GapZero memory)
    (hv : ∀ i, i < 16 → (words i).toNat = (values i).toNat)
    (h : Compression.HashState) (f : Frame)
    (hregs : f.regs = PackedHashEntry.initialRegs h)
    (hk : f.suf.konst = PackedEmit.packedK 0) :
    PackedCombine.packedCombine (Compression.embedHash h)
      (frameFrom (PackedMemoryOperands.reader
        (PackedGapInvariant.spreadWords words 16 memory)) 0 80 f).regs
      = Compression.embedHash (CompressionCorrect.compressModel values h) := by
  rw [PackedFrameFold.frameFrom_zero_80_regs _ f hk]
  change PackedCombine.packedCombine (Compression.embedHash h)
    (packedRounds (PackedOperandFold.machineWords
      (PackedGapInvariant.spreadWords words 16 memory))
      (fun i => PackedEmit.packedK (i / 16)) 80 f.regs) = _
  rw [PackedOperandFold.machine_fold memory words 80 (by decide), hregs]
  exact PackedHashEntry.compress_model memory words values hgap hv h

/-- Actual emitted operations and their decoded arithmetic result together.
This is not yet a located EVM GasSteps or a BlockKernel certificate. -/
theorem emitted_compression (memory : ByteArray) (words : Nat → UInt256)
    (values : Nat → UInt32) (hgap : PackedGapInvariant.GapZero memory)
    (hv : ∀ i, i < 16 → (words i).toNat = (values i).toNat)
    (h : Compression.HashState) (f : Frame)
    (hregs : f.regs = PackedHashEntry.initialRegs h)
    (hk : f.suf.konst = PackedEmit.packedK 0)
    (hready : Ready f) (heven : f.phase = Phase.even) (rest : List UInt256) :
    ∃ out : Frame,
      PackedStep0.runOps (PackedMemoryOperands.reader
        (PackedGapInvariant.spreadWords words 16 memory)) PackedEmit.emitRounds
        (frameStack f ++ rest) = some (frameStack out ++ rest) ∧
      PackedCombine.packedCombine (Compression.embedHash h) out.regs
        = Compression.embedHash (CompressionCorrect.compressModel values h) := by
  refine ⟨frameFrom (PackedMemoryOperands.reader
    (PackedGapInvariant.spreadWords words 16 memory)) 0 80 f, ?_, ?_⟩
  · exact PackedFullRounds.fullRounds_exec _ f hready heven rest
  · exact frame_result memory words values hgap hv h f hregs hk

/-- Specialization to the canonical entry frame discharges the frame metadata
premises. The actual entry bytecode must still establish this stack. -/
theorem initial_compression (memory : ByteArray) (words : Nat → UInt256)
    (values : Nat → UInt32) (hgap : PackedGapInvariant.GapZero memory)
    (hv : ∀ i, i < 16 → (words i).toNat = (values i).toNat)
    (h : Compression.HashState) (ret xoff xend : UInt256) (rest : List UInt256) :
    ∃ out : Frame,
      PackedStep0.runOps (PackedMemoryOperands.reader
        (PackedGapInvariant.spreadWords words 16 memory)) PackedEmit.emitRounds
        (frameStack (PackedInitialFrame.initialFrame h ret xoff xend) ++ rest)
        = some (frameStack out ++ rest) ∧
      PackedCombine.packedCombine (Compression.embedHash h) out.regs
        = Compression.embedHash (CompressionCorrect.compressModel values h) := by
  exact emitted_compression memory words values hgap hv h
    (PackedInitialFrame.initialFrame h ret xoff xend)
    (PackedInitialFrame.initialFrame_regs h ret xoff xend)
    (PackedInitialFrame.initialFrame_constant h ret xoff xend)
    (PackedInitialFrame.initialFrame_ready h ret xoff xend)
    (PackedInitialFrame.initialFrame_phase h ret xoff xend) rest

#print axioms initial_compression
#print axioms frame_result
#print axioms emitted_compression
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionExec
