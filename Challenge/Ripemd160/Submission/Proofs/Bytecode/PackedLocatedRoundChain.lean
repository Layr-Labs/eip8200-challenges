import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedEndpointPC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedInvariants
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedAllRoundExec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSequence

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Composing exact located packed rounds

This module starts the actual eighty-round composition.  It packages one
exact round with every state fact needed by the following round, proves the
artifact PC seam between ordinary adjacent rounds, and composes two such
rounds with `GasSteps.trans`.  Group-boundary swaps are intentionally handled
by the next theorem family rather than hidden in an assumed endpoint.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedRoundChain

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PackedStep0 PackedStepFrame PackedEmit PackedRoundSequence
open PackedRunOpBridge PackedRoundSites PackedLocatedEndpointPC
open PackedLocatedInvariants StackRoundTemplate

/-- Every emitted round fits under a uniform local stack allowance of 53
operations.  The frame itself always contains nineteen words. -/
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

/-- Alternating the physical register phase agrees with incrementing the
round index. -/
theorem phaseAt_succ (i : Nat) : phaseAt (i + 1) = (phaseAt i).flip := by
  unfold phaseAt
  by_cases heven : i % 2 = 0
  · have hodd : (i + 1) % 2 ≠ 0 := by omega
    simp [heven, hodd, Phase.flip]
  · have hodd : i % 2 = 1 := by omega
    have heven' : (i + 1) % 2 = 0 := by omega
    simp [heven, heven', Phase.flip]

/-- Equality with a concrete site's declared start PC supplies the bridge's
`PathStarts` fact; exact byte lookup comes from the first `LocatedSite`. -/
theorem pathStarts_of_statePC_eq_start {artifact : ProgramArtifact}
    {fork : Fork} {template : List YulEvmCompiler.Instr}
    (site : GenericRoundSite artifact fork template) (s : State)
    (hpc : s.pc = site.startPC) : PathStarts site.path s := by
  cases hsites : site.sites with
  | nil =>
      have hhead := site.head_eq
      simp [headPC, hsites] at hhead
  | cons first rest =>
      have hfirst : first.pc = site.startPC := by
        have hhead := site.head_eq
        simpa [headPC, hsites] using hhead
      simp only [GenericRoundSite.path, LocatedSite.path, hsites, List.map,
        PathStarts]
      rw [hpc, ← hfirst]
      exact first.pc_eq

/-- One exact artifact round, including the abstract frame transition and all
state fields required to start a following located block. -/
theorem round_step (round : Fin 80) (s : State)
    (frame : PackedStepFrame.Frame)
    (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = phaseAt round.val)
    (hready : Ready frame)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite round).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack (roundFrame (memoryWord s) round.val frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite round).endPC := by
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
    certificate_preserved (round_straightLine round) hbudget hstart
      hcode hfork hrun hnp habstract
  exact ⟨t, trace, htstack, hmemory, henv, hhalt, hcalls,
    round_block_endPC round s t hbudget hstart hfork hblock⟩

/-- Except at a group boundary, the exact endpoint of round `i` is the exact
start of round `i+1`.  This is a finite artifact-layout fact. -/
theorem interior_round_seam (round : Fin 80)
    (hnext : round.val + 1 < 80)
    (hinterior : (round.val + 1) % 16 ≠ 0) :
    (roundSite round).endPC =
      (roundSite ⟨round.val + 1, hnext⟩).startPC := by
  fin_cases round <;> simp_all <;> rfl

/-- One ordinary (non-boundary) round advances the abstract frame and lands
at the exact start PC of the following round. -/
theorem interior_transition (round : Fin 80)
    (hnext : round.val + 1 < 80)
    (hinterior : (round.val + 1) % 16 ≠ 0)
    (s : State) (frame : PackedStepFrame.Frame) (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = phaseAt round.val)
    (hready : Ready frame)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite round).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack
        (advanceFrame (memoryWord s) round.val frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite ⟨round.val + 1, hnext⟩).startPC := by
  obtain ⟨t, trace, htstack, hmemory, henv, hhalt, hcalls, htpc⟩ :=
    round_step round s frame rest hstack hphase hready hrest hstart
      hcode hfork hrun hnp
  refine ⟨t, trace, ?_, hmemory, henv, hhalt, hcalls,
    htpc.trans (interior_round_seam round hnext hinterior)⟩
  simpa [advanceFrame, boundaryFrame, hinterior] using htstack

/-- Two consecutive non-boundary exact round sites compose into one actual
gas-parametric trace.  All premises for the second round are derived from the
first certificate and the concrete artifact seam. -/
theorem two_interior_rounds (round : Fin 80)
    (hnext : round.val + 1 < 80)
    (hinterior : (round.val + 1) % 16 ≠ 0)
    (s : State) (frame : PackedStepFrame.Frame) (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = phaseAt round.val)
    (hready : Ready frame)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite round).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack
        (roundFrame (memoryWord s) (round.val + 1)
          (roundFrame (memoryWord s) round.val frame)) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite ⟨round.val + 1, hnext⟩).endPC := by
  obtain ⟨middle, firstTrace, hmstack, hmmemory, hmenv, hmhalt,
      hmcalls, hmpc⟩ :=
    round_step round s frame rest hstack hphase hready hrest hstart
      hcode hfork hrun hnp
  let nextRound : Fin 80 := ⟨round.val + 1, hnext⟩
  have hmiddleStart : PathStarts (roundSite nextRound).path middle := by
    apply pathStarts_of_statePC_eq_start
    exact hmpc.trans (interior_round_seam round hnext hinterior)
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
  have hnextPhase :
      (roundFrame (memoryWord s) round.val frame).phase =
        phaseAt nextRound.val := by
    rw [roundFrame, stepFrame_phase, hphase]
    exact (phaseAt_succ round.val).symm
  have hnextReady :
      Ready (roundFrame (memoryWord s) round.val frame) :=
    ready_step _ _ _ _ frame hready
  have hmemoryWord : memoryWord middle = memoryWord s := by
    funext address
    simp [memoryWord, hmmemory]
  obtain ⟨t, secondTrace, htstack, htmemory, htenv, hthalt,
      htcalls, htpc⟩ :=
    round_step nextRound middle
      (roundFrame (memoryWord s) round.val frame) rest hmstack hnextPhase
      hnextReady hrest hmiddleStart hmiddleCode hmiddleFork hmhalt hmiddleNp
  refine ⟨t, firstTrace.trans secondTrace, ?_, htmemory.trans hmmemory,
    htenv.trans hmenv, hthalt, htcalls.trans hmcalls, htpc⟩
  simpa only [hmemoryWord] using htstack

#print axioms phaseAt_succ
#print axioms pathStarts_of_statePC_eq_start
#print axioms round_step
#print axioms interior_round_seam
#print axioms interior_transition
#print axioms two_interior_rounds

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedRoundChain
