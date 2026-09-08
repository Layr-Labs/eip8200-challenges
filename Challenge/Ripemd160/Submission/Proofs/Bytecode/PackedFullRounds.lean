import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSequence
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAllRoundExec

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFullRounds
open EvmSemantics PackedStepFrame PackedStep0 PackedEmit PackedRoundSequence

/-- The real eighty-round emitter executes the frame recurrence. All ten
round-class contracts are discharged, including the four constant swaps.
This is abstract execution; artifact location and preprocessing are separate. -/
theorem fullRounds_exec (memAt : UInt256 → UInt256) (f : Frame)
    (hready : Ready f) (heven : f.phase = Phase.even) (rest : List UInt256) :
    runOps memAt emitRounds (frameStack f ++ rest)
      = some (frameStack (frameFrom memAt 0 80 f) ++ rest) := by
  have hround : ∀ i, i < 80 → ∀ f, Ready f → ∀ rest,
      runOps memAt (emitRound f.phase i) (frameStack f ++ rest)
        = some (frameStack (roundFrame memAt i f) ++ rest) := by
    intro i hi frame hf tail
    exact PackedAllRoundExec.emitted_round_exec i hi memAt frame tail hf.1 hf.2
  simpa only [emitRounds, heven] using
    emitFrom_exec memAt hround 0 80 (by decide) f hready rest

#print axioms fullRounds_exec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedFullRounds
