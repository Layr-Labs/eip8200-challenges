import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedRoundCertificate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedInvariants

set_option warningAsError true
set_option autoImplicit false

/-!
# Exact endpoint state for packed located round sites

This file closes the PC seam deliberately left open by the local round
certificate.  A successful planned block ends at its concrete site's declared
`endPC`; the result is derived from the located plan and artifact PCs, not
accepted as an extra premise.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedEndpointPC

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PackedRunOpBridge PackedStep0 StackRoundTemplate

/-- The last successful instruction of a located plan advances to the
`afterPC` recorded by the exact site list.  Earlier instructions are handled
recursively; their environment preservation transports the artifact fork
needed to form the next `EncodesOp` witness. -/
private theorem block_endPC_of_plan_sites {artifact : ProgramArtifact}
    {fork : Fork} {ops : List Op}
    {sites : List (LocatedSite artifact fork)} {s t : State} {endPC : UInt256}
    (plan : LocatedPlan ops (LocatedSite.path sites) s)
    (hfork : s.fork = fork)
    (hblock : Stepper.runLocatedBlock (LocatedSite.path sites) s = some t)
    (hend : afterPC sites = some endPC) : t.pc = endPC := by
  induction sites generalizing ops s t endPC with
  | nil => simp [afterPC] at hend
  | cons site sites ih =>
      cases ops with
      | nil => simp [LocatedPlan, LocatedSite.path] at plan
      | cons op ops =>
          change EncodesShape op site.located.instruction ∧
            s.stack.length < 1024 ∧
            s.pc.toNat = artifact.instructionPC site.located.index ∧
            ∀ next, Stepper.runInstr site.located.instruction s = some next →
              LocatedPlan ops (LocatedSite.path sites) next at plan
          rcases plan with ⟨shape, hcap, hpc, htailPlan⟩
          let encoding : EncodesOp s.fork op site.located.instruction :=
            ⟨shape, by simpa [hfork] using site.located.wellFormed⟩
          cases hstep : Stepper.runInstr site.located.instruction s with
          | none =>
              simp [LocatedSite.path, Stepper.runLocatedBlock,
                Stepper.runLocated, hpc, hstep] at hblock
          | some next =>
              have hlocated : Stepper.runLocated site.located s = some next := by
                simp [Stepper.runLocated, hpc, hstep]
              cases sites with
              | nil =>
                  have htarget : next = t := by
                    simpa only [LocatedSite.path, List.map,
                      Stepper.runLocatedBlock, hlocated, Option.some.injEq]
                      using hblock
                  subst t
                  have hstepPC := runInstr_pc_of_encoding encoding hcap hstep
                  rw [instructionNextPC_eq_add_size shape] at hstepPC
                  have hstartPC : s.pc = site.pc :=
                    Challenge.EvmProof.Word.word_ext
                      (hpc.trans site.pc_eq.symm)
                  have hendPC :
                      site.pc + UInt256.ofNat site.located.instruction.size =
                        endPC := by
                    simpa [afterPC] using hend
                  calc
                    next.pc = s.pc +
                        UInt256.ofNat site.located.instruction.size := hstepPC
                    _ = site.pc +
                        UInt256.ofNat site.located.instruction.size := by
                          rw [hstartPC]
                    _ = endPC := hendPC
              | cons nextSite rest =>
                  have hnextRunning : next.halt = .Running := by
                    cases hhalt : next.halt <;>
                      simp_all [LocatedSite.path, Stepper.runLocatedBlock]
                  have htailBlock :
                      Stepper.runLocatedBlock
                        (LocatedSite.path (nextSite :: rest)) next = some t := by
                    simpa only [LocatedSite.path, List.map,
                      Stepper.runLocatedBlock, hlocated, hnextRunning]
                      using hblock
                  have hnextFork : next.fork = fork := by
                    change next.executionEnv.fork = fork
                    rw [Stepper.runInstr_executionEnv hstep]
                    exact hfork
                  have hendTail :
                      afterPC (nextSite :: rest) = some endPC := by
                    simpa only [afterPC] using hend
                  exact ih (htailPlan next hstep) hnextFork htailBlock hendTail

/-- A successful block for a planned concrete site finishes at that site's
declared endpoint.  No final-state or arithmetic-evaluator premise is used. -/
theorem block_endPC {artifact : ProgramArtifact} {fork : Fork}
    {ops : List Op} {template : List Instr}
    (site : GenericRoundSite artifact fork template) (s t : State)
    (plan : LocatedPlan ops site.path s) (hfork : s.fork = fork)
    (hblock : Stepper.runLocatedBlock site.path s = some t) :
    t.pc = site.endPC := by
  exact block_endPC_of_plan_sites plan hfork hblock site.end_eq

/-- Exact endpoint PC for any of the eighty final-artifact round blocks. -/
theorem round_block_endPC (round : Fin 80) (s t : State)
    (hbudget : s.stack.length +
      (PackedEmit.emitRound (PackedRoundSites.phaseAt round.val) round.val).length <
        1024)
    (hstart : PathStarts (PackedRoundSites.roundSite round).path s)
    (hfork : s.fork = .Osaka)
    (hblock : Stepper.runLocatedBlock
      (PackedRoundSites.roundSite round).path s = some t) :
    t.pc = (PackedRoundSites.roundSite round).endPC := by
  apply block_endPC (PackedRoundSites.roundSite round) s t
    (locatedPlan_of_straightLine (PackedRoundSites.round_straightLine round)
      hbudget hstart hfork) hfork hblock

#print axioms block_endPC
#print axioms round_block_endPC

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedEndpointPC
