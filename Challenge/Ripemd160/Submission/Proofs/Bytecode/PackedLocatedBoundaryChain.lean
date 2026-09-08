import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedRoundChain
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBoundarySites

set_option warningAsError true
set_option autoImplicit false

/-!
# Exact packed group-boundary trace composition

Four round exits are followed by a three-instruction constant replacement.
This module composes the exact round and exact boundary certificates and lands
at the next round's concrete artifact PC.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedBoundaryChain

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PackedStep0 PackedStepFrame PackedEmit PackedRoundSequence
open PackedRunOpBridge PackedRoundSites PackedBoundarySites
open PackedLocatedEndpointPC PackedLocatedInvariants StackRoundTemplate
open PackedLocatedRoundChain

/-- Last round of the group preceding a boundary. -/
def boundaryRound (boundary : Fin 4) : Fin 80 :=
  ⟨16 * boundary.val + 15, by have := boundary.isLt; omega⟩

/-- First round following a boundary. -/
def postBoundaryRound (boundary : Fin 4) : Fin 80 :=
  ⟨16 * (boundary.val + 1), by have := boundary.isLt; omega⟩

/-- Exact artifact seam from a group's last round into its constant swap. -/
theorem round_boundary_seam (boundary : Fin 4) :
    (roundSite (boundaryRound boundary)).endPC =
      (boundarySite boundary).startPC := by
  fin_cases boundary <;> rfl

/-- Exact artifact seam from a constant swap into the next group's round. -/
theorem boundary_round_seam (boundary : Fin 4) :
    (boundarySite boundary).endPC =
      (roundSite (postBoundaryRound boundary)).startPC := by
  fin_cases boundary <;> rfl

private theorem boundary_budget (boundary : Fin 4)
    (frame : PackedStepFrame.Frame)
    (rest : List UInt256) (hrest : rest.length + 72 < 1024) :
    (frameStack frame ++ rest).length +
      (kSwap (boundary.val + 1)).length < 1024 := by
  rw [List.length_append, frameStack_length, kSwap_length]
  omega

/-- One exact boundary block with every preserved field and its concrete exit
PC. -/
theorem boundary_step (boundary : Fin 4) (s : State)
    (frame : PackedStepFrame.Frame)
    (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (boundarySite boundary).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack
        (replaceK (packedK (boundary.val + 1)) frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (boundarySite boundary).endPC := by
  have hbudget : s.stack.length + (kSwap (boundary.val + 1)).length < 1024 := by
    rw [hstack]
    exact boundary_budget boundary frame rest hrest
  have habstract : runOps (memoryWord s) (kSwap (boundary.val + 1)) s.stack =
      some (frameStack
        (replaceK (packedK (boundary.val + 1)) frame) ++ rest) := by
    rw [hstack]
    exact kSwap_exec (memoryWord s) (boundary.val + 1) frame rest
  obtain ⟨t, hblock, trace, htstack, hmemory, henv, hhalt, hcalls⟩ :=
    certificate_preserved (boundary_straightLine boundary) hbudget hstart
      hcode hfork hrun hnp habstract
  have plan := locatedPlan_of_straightLine (boundary_straightLine boundary)
    hbudget hstart hfork
  exact ⟨t, trace, htstack, hmemory, henv, hhalt, hcalls,
    block_endPC (boundarySite boundary) s t plan hfork hblock⟩

private theorem advanceFrame_at_boundary (boundary : Fin 4)
    (memAt : UInt256 → UInt256) (frame : PackedStepFrame.Frame) :
    advanceFrame memAt (boundaryRound boundary).val frame =
      replaceK (packedK (boundary.val + 1))
        (roundFrame memAt (boundaryRound boundary).val frame) := by
  fin_cases boundary <;> rfl

/-- Execute the last round of a group and its exact constant-swap block,
landing at the next round's artifact start. -/
theorem boundary_transition (boundary : Fin 4) (s : State)
    (frame : PackedStepFrame.Frame)
    (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hphase : frame.phase = phaseAt (boundaryRound boundary).val)
    (hready : Ready frame)
    (hrest : rest.length + 72 < 1024)
    (hstart : PathStarts (roundSite (boundaryRound boundary)).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps s t,
      t.stack = frameStack
        (advanceFrame (memoryWord s) (boundaryRound boundary).val frame) ++ rest ∧
      t.memory = s.memory ∧ t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧ t.callStack = s.callStack ∧
      t.pc = (roundSite (postBoundaryRound boundary)).startPC := by
  obtain ⟨middle, roundTrace, hmstack, hmmemory, hmenv, hmhalt,
      hmcalls, hmpc⟩ :=
    round_step (boundaryRound boundary) s frame rest hstack hphase hready
      hrest hstart hcode hfork hrun hnp
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
      htcalls, htpc⟩ :=
    boundary_step boundary middle
      (roundFrame (memoryWord s) (boundaryRound boundary).val frame) rest
      hmstack hrest hmiddleStart hmiddleCode hmiddleFork hmhalt hmiddleNp
  refine ⟨t, roundTrace.trans boundaryTrace, ?_, htmemory.trans hmmemory,
    htenv.trans hmenv, hthalt, htcalls.trans hmcalls,
    htpc.trans (boundary_round_seam boundary)⟩
  rw [advanceFrame_at_boundary]
  exact htstack

/-- Uniform one-round transition used by the eighty-round induction.  The
four modular-boundary cases select the proved swap block; every other case
uses the ordinary round transition. -/
theorem round_transition (round : Fin 80)
    (hnext : round.val + 1 < 80)
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
  by_cases hinterior : (round.val + 1) % 16 ≠ 0
  · exact interior_transition round hnext hinterior s frame rest hstack
      hphase hready hrest hstart hcode hfork hrun hnp
  · have hmod : (round.val + 1) % 16 = 0 := by omega
    have hcases : round.val = 15 ∨ round.val = 31 ∨ round.val = 47 ∨
        round.val = 63 := by
      have := round.isLt
      omega
    rcases hcases with h15 | h31 | h47 | h63
    · have hr : round = boundaryRound (0 : Fin 4) := Fin.ext h15
      subst round
      simpa [boundaryRound, postBoundaryRound] using
        boundary_transition (0 : Fin 4) s frame rest hstack hphase hready
          hrest hstart hcode hfork hrun hnp
    · have hr : round = boundaryRound (1 : Fin 4) := Fin.ext h31
      subst round
      simpa [boundaryRound, postBoundaryRound] using
        boundary_transition (1 : Fin 4) s frame rest hstack hphase hready
          hrest hstart hcode hfork hrun hnp
    · have hr : round = boundaryRound (2 : Fin 4) := Fin.ext h47
      subst round
      simpa [boundaryRound, postBoundaryRound] using
        boundary_transition (2 : Fin 4) s frame rest hstack hphase hready
          hrest hstart hcode hfork hrun hnp
    · have hr : round = boundaryRound (3 : Fin 4) := Fin.ext h63
      subst round
      simpa [boundaryRound, postBoundaryRound] using
        boundary_transition (3 : Fin 4) s frame rest hstack hphase hready
          hrest hstart hcode hfork hrun hnp

#print axioms round_boundary_seam
#print axioms boundary_round_seam
#print axioms boundary_step
#print axioms boundary_transition
#print axioms round_transition

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedBoundaryChain
