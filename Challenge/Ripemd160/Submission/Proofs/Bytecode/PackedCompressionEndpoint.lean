import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionExec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFrameControl

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionEndpoint
open EvmSemantics PackedStepFrame PackedRoundSequence PackedInitialFrame

/-- Explicit end frame for the real eighty-round operation sequence. -/
def endpoint (memory : ByteArray) (words : Nat → UInt256)
    (h : Compression.HashState) (ret xoff xend : UInt256) : Frame :=
  frameFrom (PackedMemoryOperands.reader
    (PackedGapInvariant.spreadWords words 16 memory)) 0 80
    (initialFrame h ret xoff xend)

theorem endpoint_exec (memory : ByteArray) (words : Nat → UInt256)
    (h : Compression.HashState) (ret xoff xend : UInt256) (rest : List UInt256) :
    PackedStep0.runOps (PackedMemoryOperands.reader
      (PackedGapInvariant.spreadWords words 16 memory)) PackedEmit.emitRounds
      (frameStack (initialFrame h ret xoff xend) ++ rest) =
        some (frameStack (endpoint memory words h ret xoff xend) ++ rest) :=
  PackedFullRounds.fullRounds_exec _ (initialFrame h ret xoff xend)
    (initialFrame_ready _ _ _ _) (initialFrame_phase _ _ _ _) rest

/-- The combine consumer sees even register order, group-four constant and
unchanged return/range metadata. This states the full concrete stack shape. -/
theorem endpoint_stack (memory : ByteArray) (words : Nat → UInt256)
    (h : Compression.HashState) (ret xoff xend : UInt256) :
    frameStack (endpoint memory words h ret xoff xend) =
      regsStack Phase.even (endpoint memory words h ret xoff xend).regs ++
        suffixStack (PackedFrameControl.finalSuffix ret xoff xend) := by
  unfold frameStack
  rw [show (endpoint memory words h ret xoff xend).phase = Phase.even from
    PackedFrameControl.initialFrame_finalPhase _ h ret xoff xend]
  rw [show (endpoint memory words h ret xoff xend).suf =
      PackedFrameControl.finalSuffix ret xoff xend from
    PackedFrameControl.initialFrame_finalSuffix _ h ret xoff xend]

theorem endpoint_result (memory : ByteArray) (words : Nat → UInt256)
    (values : Nat → UInt32) (hgap : PackedGapInvariant.GapZero memory)
    (hv : ∀ i, i < 16 → (words i).toNat = (values i).toNat)
    (h : Compression.HashState) (ret xoff xend : UInt256) :
    PackedCombine.packedCombine (Compression.embedHash h)
      (endpoint memory words h ret xoff xend).regs =
        Compression.embedHash (CompressionCorrect.compressModel values h) :=
  PackedCompressionExec.frame_result memory words values hgap hv h
    (initialFrame h ret xoff xend) (initialFrame_regs _ _ _ _)
    (initialFrame_constant _ _ _ _)

#print axioms endpoint_exec
#print axioms endpoint_stack
#print axioms endpoint_result
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionEndpoint
