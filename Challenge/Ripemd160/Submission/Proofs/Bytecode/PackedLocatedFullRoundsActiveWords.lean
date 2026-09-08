import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedFullRounds
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedActiveWords

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Active-memory extent through the exact eighty-round trace

This is a parallel strengthening of `PackedLocatedFullRounds.full_rounds`.
The original theorem is intentionally unchanged.  Each local block retains
its successful `runLocatedBlock` witness long enough to apply the exact-opcode
active-word monotonicity theorem, and the inequalities are then threaded over
ordinary and boundary transitions.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedFullRoundsActiveWords

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PackedStep0 PackedStepFrame PackedEmit PackedRoundSequence
open PackedRunOpBridge PackedRoundSites StackRoundTemplate
open PackedLocatedEndpointPC PackedLocatedInvariants
open PackedLocatedActiveWords PackedLocatedRoundChain
open PackedLocatedBoundaryChain
open PackedBoundarySites PackedBoundarySwap

private theorem emitRound_length_le_53 (round : Fin 80) :
    (emitRound (phaseAt round.val) round.val).length ≤ 53 := by
  fin_cases round <;> decide

private theorem round_budget (round : Fin 80) (frame : PackedStepFrame.Frame)
    (rest : List UInt256) (hrest : rest.length + 72 < 1024) :
    (frameStack frame ++ rest).length +
      (emitRound (phaseAt round.val) round.val).length < 1024 := by
  rw [List.length_append, frameStack_length]
  have hlen := emitRound_length_le_53 round
  omega

/-- One exact round, strengthened only with the active-memory inequality. -/
theorem round_step_active (round : Fin 80) (s : State)
    (frame : PackedStepFrame.Frame) (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = phaseAt round.val)
    (hready : Ready frame)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite round).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack (roundFrame (memoryWord s) round.val frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite round).endPC ∧
      s.activeWords.toNat ≤ t.activeWords.toNat := by
  have hbudget : s.stack.length +
      (emitRound (phaseAt round.val) round.val).length < 1024 := by
    rw [hstack]
    exact round_budget round frame rest hrest
  have habstract : runOps (memoryWord s)
      (emitRound (phaseAt round.val) round.val) s.stack =
        some (frameStack (roundFrame (memoryWord s) round.val frame) ++ rest) := by
    rw [hstack, ← hphase]
    simpa only [roundFrame] using
      PackedAllRoundExec.emitted_round_exec round.val round.isLt
        (memoryWord s) frame rest hready.1 hready.2
  obtain ⟨t, hblock, trace, htstack, hmemory, henv, hhalt, hcalls⟩ :=
    certificate_preserved (round_straightLine round) hbudget hstart hcode
      hfork hrun hnp habstract
  have plan := locatedPlan_of_straightLine (round_straightLine round)
    hbudget hstart hfork
  exact ⟨t, trace, htstack, hmemory, henv, hhalt, hcalls,
    round_block_endPC round s t hbudget hstart hfork hblock,
    block_activeWords_mono plan hfork hrun hblock⟩

/-- Ordinary-round transition with monotone active memory. -/
theorem interior_transition_active (round : Fin 80)
    (hnext : round.val + 1 < 80)
    (hinterior : (round.val + 1) % 16 ≠ 0)
    (s : State) (frame : PackedStepFrame.Frame) (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = phaseAt round.val) (hready : Ready frame)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite round).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack (advanceFrame (memoryWord s) round.val frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite ⟨round.val + 1, hnext⟩).startPC ∧
      s.activeWords.toNat ≤ t.activeWords.toNat := by
  obtain ⟨t, trace, htstack, hmemory, henv, hhalt, hcalls, htpc, hactive⟩ :=
    round_step_active round s frame rest hstack hphase hready hrest hstart
      hcode hfork hrun hnp
  refine ⟨t, trace, ?_, hmemory, henv, hhalt, hcalls,
    htpc.trans (interior_round_seam round hnext hinterior), hactive⟩
  simpa [advanceFrame, boundaryFrame, hinterior] using htstack

private theorem boundary_budget (boundary : Fin 4)
    (frame : PackedStepFrame.Frame) (rest : List UInt256)
    (hrest : rest.length + 72 < 1024) :
    (frameStack frame ++ rest).length +
      (kSwap (boundary.val + 1)).length < 1024 := by
  rw [List.length_append, frameStack_length, kSwap_length]
  omega

/-- One exact constant-swap block with monotone active memory. -/
theorem boundary_step_active (boundary : Fin 4) (s : State)
    (frame : PackedStepFrame.Frame) (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (boundarySite boundary).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack
        (replaceK (packedK (boundary.val + 1)) frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (boundarySite boundary).endPC ∧
      s.activeWords.toNat ≤ t.activeWords.toNat := by
  have hbudget : s.stack.length + (kSwap (boundary.val + 1)).length < 1024 := by
    rw [hstack]
    exact boundary_budget boundary frame rest hrest
  have habstract : runOps (memoryWord s) (kSwap (boundary.val + 1)) s.stack =
      some (frameStack
        (replaceK (packedK (boundary.val + 1)) frame) ++ rest) := by
    rw [hstack]
    exact PackedBoundarySwap.kSwap_exec
      (memoryWord s) (boundary.val + 1) frame rest
  obtain ⟨t, hblock, trace, htstack, hmemory, henv, hhalt, hcalls⟩ :=
    certificate_preserved (boundary_straightLine boundary) hbudget hstart
      hcode hfork hrun hnp habstract
  have plan := locatedPlan_of_straightLine (boundary_straightLine boundary)
    hbudget hstart hfork
  exact ⟨t, trace, htstack, hmemory, henv, hhalt, hcalls,
    block_endPC (boundarySite boundary) s t plan hfork hblock,
    block_activeWords_mono plan hfork hrun hblock⟩

private theorem advanceFrame_at_boundary (boundary : Fin 4)
    (memAt : UInt256 → UInt256) (frame : PackedStepFrame.Frame) :
    advanceFrame memAt (boundaryRound boundary).val frame =
      replaceK (packedK (boundary.val + 1))
        (roundFrame memAt (boundaryRound boundary).val frame) := by
  fin_cases boundary <;> rfl

/-- Boundary-round plus constant-swap transition, retaining active-word
monotonicity over both exact blocks. -/
theorem boundary_transition_active (boundary : Fin 4) (s : State)
    (frame : PackedStepFrame.Frame) (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = phaseAt (boundaryRound boundary).val)
    (hready : Ready frame) (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite (boundaryRound boundary)).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack
        (advanceFrame (memoryWord s) (boundaryRound boundary).val frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite (postBoundaryRound boundary)).startPC ∧
      s.activeWords.toNat ≤ t.activeWords.toNat := by
  obtain ⟨middle, roundTrace, hmstack, hmmemory, hmenv, hmhalt,
      hmcalls, hmpc, hmactive⟩ :=
    round_step_active (boundaryRound boundary) s frame rest hstack hphase
      hready hrest hstart hcode hfork hrun hnp
  have hmiddleStart : PathStarts (boundarySite boundary).path middle := by
    apply pathStarts_of_statePC_eq_start
    exact hmpc.trans (round_boundary_seam boundary)
  have hmiddleCode :
      middle.executionEnv.code = Artifact.submissionArtifact.code := by
    rw [hmenv]
    exact hcode
  have hmiddleFork : middle.fork = .Osaka := by
    change middle.executionEnv.fork = .Osaka
    rw [hmenv]
    exact hfork
  have hmiddleNp :
      Precompile.isPrecompileWithConfig middle.executionEnv.precompileConfig
        middle.executionEnv.fork middle.executionEnv.codeAddr = false := by
    simpa only [hmenv] using hnp
  obtain ⟨t, boundaryTrace, htstack, htmemory, htenv, hthalt,
      htcalls, htpc, htactive⟩ :=
    boundary_step_active boundary middle
      (roundFrame (memoryWord s) (boundaryRound boundary).val frame) rest
      hmstack hrest hmiddleStart hmiddleCode hmiddleFork hmhalt hmiddleNp
  refine ⟨t, roundTrace.trans boundaryTrace, ?_,
    htmemory.trans hmmemory, htenv.trans hmenv, hthalt,
    htcalls.trans hmcalls, htpc.trans (boundary_round_seam boundary),
    hmactive.trans htactive⟩
  rw [advanceFrame_at_boundary]
  exact htstack

/-- Uniform next-round transition with active-word monotonicity. -/
theorem round_transition_active (round : Fin 80)
    (hnext : round.val + 1 < 80) (s : State)
    (frame : PackedStepFrame.Frame) (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = phaseAt round.val) (hready : Ready frame)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite round).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack (advanceFrame (memoryWord s) round.val frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite ⟨round.val + 1, hnext⟩).startPC ∧
      s.activeWords.toNat ≤ t.activeWords.toNat := by
  by_cases hinterior : (round.val + 1) % 16 ≠ 0
  · exact interior_transition_active round hnext hinterior s frame rest
      hstack hphase hready hrest hstart hcode hfork hrun hnp
  · have hcases : round.val = 15 ∨ round.val = 31 ∨ round.val = 47 ∨
        round.val = 63 := by
      have := round.isLt
      have hmod : (round.val + 1) % 16 = 0 := by omega
      omega
    rcases hcases with h15 | h31 | h47 | h63
    · have hr : round = boundaryRound (0 : Fin 4) := Fin.ext h15
      subst round
      simpa [boundaryRound, postBoundaryRound] using
        boundary_transition_active (0 : Fin 4) s frame rest hstack hphase
          hready hrest hstart hcode hfork hrun hnp
    · have hr : round = boundaryRound (1 : Fin 4) := Fin.ext h31
      subst round
      simpa [boundaryRound, postBoundaryRound] using
        boundary_transition_active (1 : Fin 4) s frame rest hstack hphase
          hready hrest hstart hcode hfork hrun hnp
    · have hr : round = boundaryRound (2 : Fin 4) := Fin.ext h47
      subst round
      simpa [boundaryRound, postBoundaryRound] using
        boundary_transition_active (2 : Fin 4) s frame rest hstack hphase
          hready hrest hstart hcode hfork hrun hnp
    · have hr : round = boundaryRound (3 : Fin 4) := Fin.ext h63
      subst round
      simpa [boundaryRound, postBoundaryRound] using
        boundary_transition_active (3 : Fin 4) s frame rest hstack hphase
          hready hrest hstart hcode hfork hrun hnp

/-- Starting at exact round `i`, execute the remaining rounds and retain the
initial-to-final active-word inequality. -/
theorem rounds_to_end_active (count i : Nat) (hi : i < 80)
    (hsum : i + count = 80) (hpositive : 0 < count)
    (s : State) (frame : PackedStepFrame.Frame) (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = phaseAt i) (hready : Ready frame)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite ⟨i, hi⟩).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack (frameFrom (memoryWord s) i count frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite (79 : Fin 80)).endPC ∧
      s.activeWords.toNat ≤ t.activeWords.toNat := by
  induction count generalizing i s frame with
  | zero => omega
  | succ count ih =>
      cases count with
      | zero =>
          have hi79 : i = 79 := by omega
          subst i
          obtain ⟨t, trace, htstack, hmemory, henv, hhalt, hcalls,
              htpc, hactive⟩ :=
            round_step_active (79 : Fin 80) s frame rest hstack hphase
              hready hrest hstart hcode hfork hrun hnp
          refine ⟨t, trace, ?_, hmemory, henv, hhalt, hcalls, htpc, hactive⟩
          simpa [frameFrom, advanceFrame, boundaryFrame] using htstack
      | succ count =>
          have hnext : i + 1 < 80 := by omega
          let current : Fin 80 := ⟨i, hi⟩
          obtain ⟨middle, firstTrace, hmstack, hmmemory, hmenv, hmhalt,
              hmcalls, hmpc, hmactive⟩ :=
            round_transition_active current hnext s frame rest hstack hphase
              hready hrest hstart hcode hfork hrun hnp
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
              htcalls, htpc, htactive⟩ :=
            ih (i := i + 1) (hi := hnext) (by omega) (by omega) middle
              (advanceFrame (memoryWord s) i frame) hmstack hnextPhase
              hnextReady hmiddleStart hmiddleCode hmiddleFork hmhalt hmiddleNp
          have hmemoryWord : memoryWord middle = memoryWord s := by
            funext address
            simp [memoryWord, hmmemory]
          rw [hmemoryWord] at htstack
          refine ⟨t, firstTrace.trans tailTrace, ?_,
            htmemory.trans hmmemory, htenv.trans hmenv, hthalt,
            htcalls.trans hmcalls, htpc, hmactive.trans htactive⟩
          simpa only [frameFrom] using htstack

/-- Exact full eighty-round trace plus preservation of any incoming lower
bound on `activeWords`. -/
theorem full_rounds_active (s : State) (frame : PackedStepFrame.Frame)
    (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = Phase.even) (hready : Ready frame)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite (0 : Fin 80)).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack (frameFrom (memoryWord s) 0 80 frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite (79 : Fin 80)).endPC ∧
      s.activeWords.toNat ≤ t.activeWords.toNat := by
  apply rounds_to_end_active 80 0 (by decide) (by decide) (by decide)
    s frame rest hstack
  · simpa [phaseAt] using hphase
  · exact hready
  · exact hrest
  · exact hstart
  · exact hcode
  · exact hfork
  · exact hrun
  · exact hnp

/-- A lower bound present at round zero is therefore available at the exact
round-79 endpoint.  In particular callers may instantiate `lower = 16` for
the packed final-combine stores. -/
theorem full_rounds_activeWords_ge (lower : Nat) (s : State)
    (frame : PackedStepFrame.Frame) (rest : List UInt256)
    (hlower : lower ≤ s.activeWords.toNat)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = Phase.even) (hready : Ready frame)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite (0 : Fin 80)).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack (frameFrom (memoryWord s) 0 80 frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite (79 : Fin 80)).endPC ∧
      lower ≤ t.activeWords.toNat := by
  obtain ⟨t, trace, hstack', hmemory, henv, hhalt, hcalls, hpc, hmono⟩ :=
    full_rounds_active s frame rest hstack hphase hready hrest hstart hcode
      hfork hrun hnp
  exact ⟨t, trace, hstack', hmemory, henv, hhalt, hcalls, hpc,
    hlower.trans hmono⟩

#print axioms round_step_active
#print axioms boundary_step_active
#print axioms round_transition_active
#print axioms rounds_to_end_active
#print axioms full_rounds_active
#print axioms full_rounds_activeWords_ge

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedFullRoundsActiveWords
