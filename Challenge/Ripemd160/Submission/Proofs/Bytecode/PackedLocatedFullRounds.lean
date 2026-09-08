import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedBoundaryChain

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Full exact located trace for all remaining packed rounds

The induction below threads existential concrete EVM states.  Each recursive
step invokes the already proved local `round_transition`, so the stack limit
is discharged afresh from the nineteen-word frame plus at most 53 round ops.
It never constructs a coarse plan for the concatenated ~4k-op body.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedFullRounds

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PackedStep0 PackedStepFrame PackedEmit PackedRoundSequence
open PackedRunOpBridge PackedRoundSites StackRoundTemplate
open PackedLocatedRoundChain PackedLocatedBoundaryChain

/-- Starting at exact round `i`, execute exactly the remaining `count` rounds
through round 79, including all intervening constant swaps. -/
theorem rounds_to_end (count i : Nat) (hi : i < 80)
    (hsum : i + count = 80) (hpositive : 0 < count)
    (s : State) (frame : PackedStepFrame.Frame) (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = phaseAt i)
    (hready : Ready frame)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite ⟨i, hi⟩).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack (frameFrom (memoryWord s) i count frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite (79 : Fin 80)).endPC := by
  induction count generalizing i s frame with
  | zero => omega
  | succ count ih =>
      cases count with
      | zero =>
          have hi79 : i = 79 := by omega
          subst i
          obtain ⟨t, trace, htstack, hmemory, henv, hhalt, hcalls, htpc⟩ :=
            round_step (79 : Fin 80) s frame rest hstack hphase hready
              hrest hstart hcode hfork hrun hnp
          refine ⟨t, trace, ?_, hmemory, henv, hhalt, hcalls, htpc⟩
          simpa [frameFrom, advanceFrame, boundaryFrame] using htstack
      | succ count =>
          have hnext : i + 1 < 80 := by omega
          let current : Fin 80 := ⟨i, hi⟩
          obtain ⟨middle, firstTrace, hmstack, hmmemory, hmenv, hmhalt,
              hmcalls, hmpc⟩ :=
            round_transition current hnext s frame rest hstack hphase hready
              hrest hstart hcode hfork hrun hnp
          have hmiddleStart :
              PathStarts (roundSite ⟨i + 1, hnext⟩).path middle :=
            pathStarts_of_statePC_eq_start _ middle hmpc
          have hmiddleCode :
              middle.executionEnv.code = Artifact.submissionArtifact.code := by
            rw [hmenv]
            exact hcode
          have hmiddleFork : middle.fork = .Osaka := by
            change middle.executionEnv.fork = .Osaka
            rw [hmenv]
            exact hfork
          have hmiddleNp :
              Precompile.isPrecompileWithConfig
                middle.executionEnv.precompileConfig middle.executionEnv.fork
                middle.executionEnv.codeAddr = false := by
            simpa only [hmenv] using hnp
          have hnextPhase :
              (advanceFrame (memoryWord s) i frame).phase = phaseAt (i + 1) := by
            rw [phase_advance, hphase]
            exact (phaseAt_succ i).symm
          have hnextReady : Ready (advanceFrame (memoryWord s) i frame) :=
            ready_advance (memoryWord s) i frame hready
          obtain ⟨t, tailTrace, htstack, htmemory, htenv, hthalt,
              htcalls, htpc⟩ :=
            ih (i := i + 1) (hi := hnext) (by omega) (by omega) middle
              (advanceFrame (memoryWord s) i frame) hmstack hnextPhase
              hnextReady hmiddleStart hmiddleCode hmiddleFork hmhalt hmiddleNp
          have hmemoryWord : memoryWord middle = memoryWord s := by
            funext address
            simp [memoryWord, hmmemory]
          rw [hmemoryWord] at htstack
          refine ⟨t, firstTrace.trans tailTrace, ?_,
            htmemory.trans hmmemory, htenv.trans hmenv, hthalt,
            htcalls.trans hmcalls, htpc⟩
          simpa only [frameFrom] using htstack

/-- The exact eighty-round packed body, from round-zero entry through the
round-79 endpoint. -/
theorem full_rounds (s : State) (frame : PackedStepFrame.Frame)
    (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = Phase.even)
    (hready : Ready frame)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite (0 : Fin 80)).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack (frameFrom (memoryWord s) 0 80 frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite (79 : Fin 80)).endPC := by
  apply rounds_to_end 80 0 (by decide) (by decide) (by decide) s frame rest
    hstack
  · simpa [phaseAt] using hphase
  · exact hready
  · exact hrest
  · exact hstart
  · exact hcode
  · exact hfork
  · exact hrun
  · exact hnp

#print axioms rounds_to_end
#print axioms full_rounds

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedFullRounds
