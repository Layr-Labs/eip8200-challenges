import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityQuadGroup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityPCTransport

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace CavityQuadGroup CavityPCTransport

theorem runInstrSeq_result_pc (code : List Instr)
    (hform : ∀ i ∈ code, PairMultiplyLift.Advances i)
    {s t : State} (hresult : runInstrSeq code s = some t) :
    t.pc = pcAfter s.pc code := by
  have h := runInstrSeq_relocate code hform s s.pc
  have hself : {s with pc := s.pc} = s := rfl
  rw [hself, hresult, Option.map_some] at h
  exact congrArg State.pc (Option.some.inj h)

theorem runInstrSeq_executionEnv (code : List Instr) {s t : State}
    (hresult : runInstrSeq code s = some t) : t.executionEnv = s.executionEnv := by
  induction code generalizing s with
  | nil =>
      cases hresult
      rfl
  | cons instruction rest ih =>
      cases hstep : Stepper.runInstr instruction s with
      | none => simp [runInstrSeq, hstep] at hresult
      | some next =>
          have henv := Stepper.runInstr_executionEnv hstep
          cases rest with
          | nil =>
              have heq : next = t := by simpa [runInstrSeq, hstep] using hresult
              exact heq ▸ henv
          | cons a tail =>
              cases hhalt : next.halt <;> simp [runInstrSeq, hstep, hhalt] at hresult
              exact (ih hresult).trans henv

theorem site_end {artifact : ProgramArtifact} {fork : Fork} {code : List Instr}
    (site : GenericRoundSite artifact fork code) :
    site.endPC = pcAfter site.startPC code := by
  have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
    site.head_eq site.end_eq site.contiguous
  rwa [site.instruction_eq] at h

/-- Splice one certified bridge into a known pure computation. The continuation
receives the relocated suffix result, allowing this lemma to handle any number
of fragments by nesting, without unfolding arithmetic at the cut. -/
noncomputable def gasSteps_splice {artifact : ProgramArtifact} {fork : Fork}
    (first remaining : List Instr)
    (site : GenericRoundSite artifact fork first) (bridge : Bridge artifact fork)
    (hbridge : bridge.push.pc = site.endPC)
    (hfirst : ∀ i ∈ first, PairMultiplyLift.Advances i)
    (hremaining : ∀ i ∈ remaining, PairMultiplyLift.Advances i)
    (s result finish : State) (hpc : s.pc = site.startPC)
    (hwhole : runInstrSeq (first ++ remaining) s = some result)
    (hcap : ∀ middle, runInstrSeq first s = some middle → middle.stack.length < 1023)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (continuation : ∀ middle, middle.pc = bridge.destination.pc.succ →
      middle.executionEnv = s.executionEnv → middle.halt = .Running →
      runInstrSeq remaining middle =
        some {result with pc := pcAfter middle.pc remaining} →
      GasSteps middle finish) : GasSteps s finish := by
  let split := runInstrSeq_split first remaining hfirst hrun hwhole
  let middle := Classical.choose split
  have hmiddle := Classical.choose_spec split
  have hprefix : runInstrSeq first s = some middle := hmiddle.1
  have hrunMiddle : middle.halt = .Running := hmiddle.2.1
  have hsuffix : runInstrSeq remaining middle = some result := hmiddle.2.2
  have hpcMiddle : middle.pc = site.endPC := by
    rw [runInstrSeq_result_pc first hfirst hprefix, hpc, ← site_end site]
  have henvMiddle : middle.executionEnv = s.executionEnv :=
    runInstrSeq_executionEnv first hprefix
  have gfirst : GasSteps s middle := by
    apply Stepper.runLocatedBlock_sound artifact fork site.path hcode hfork
    · rw [PairMultiplyLift.runLocatedBlock_eq_raw site hfirst s hpc]
      exact hprefix
    · exact hrun
    · exact hnp
  have hcodeMiddle : middle.executionEnv.code = artifact.code := by
    rw [henvMiddle]
    exact hcode
  have hforkMiddle : middle.fork = fork := by
    change middle.executionEnv.fork = fork
    rw [henvMiddle]
    exact hfork
  have hnpMiddle : Precompile.isPrecompileWithConfig middle.executionEnv.precompileConfig
      middle.executionEnv.fork middle.executionEnv.codeAddr = false := by
    rw [henvMiddle]
    exact hnp
  let relocated : State := {middle with pc := bridge.destination.pc.succ}
  have gbridge : GasSteps middle relocated := by
    have g := gasSteps_bridge bridge middle middle.stack (hcap middle hprefix)
      hcodeMiddle hforkMiddle hrunMiddle hnpMiddle
    apply g.cast
    · rw [hbridge, ← hpcMiddle]
    · rfl
  have hsuffixRelocated : runInstrSeq remaining relocated =
      some {result with pc := pcAfter relocated.pc remaining} := by
    have h := runInstrSeq_relocate remaining hremaining middle bridge.destination.pc.succ
    rw [hsuffix, Option.map_some] at h
    exact h
  exact (gfirst.trans gbridge).trans
    (continuation relocated rfl henvMiddle hrunMiddle hsuffixRelocated)

/-- The two-fragment case, with an explicit intermediate stack-cap premise. -/
noncomputable def gasSteps_twoPieces {artifact : ProgramArtifact} {fork : Fork}
    (first second : List Instr)
    (firstSite : GenericRoundSite artifact fork first)
    (secondSite : GenericRoundSite artifact fork second)
    (bridge : Bridge artifact fork)
    (hbridge : bridge.push.pc = firstSite.endPC)
    (hsecondPC : secondSite.startPC = bridge.destination.pc.succ)
    (hfirst : ∀ i ∈ first, PairMultiplyLift.Advances i)
    (hsecond : ∀ i ∈ second, PairMultiplyLift.Advances i)
    (s result : State) (hpc : s.pc = firstSite.startPC)
    (hwhole : runInstrSeq (first ++ second) s = some result)
    (hcap : ∀ middle, runInstrSeq first s = some middle → middle.stack.length < 1023)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s {result with pc := secondSite.endPC} := by
  apply gasSteps_splice first second firstSite bridge hbridge hfirst hsecond
    s result {result with pc := secondSite.endPC} hpc hwhole hcap hcode hfork hrun hnp
  intro middle hmidPC henv hmidRun hraw
  have hpc' : middle.pc = secondSite.startPC := hmidPC.trans hsecondPC.symm
  have hraw' : runInstrSeq second middle = some {result with pc := secondSite.endPC} := by
    rw [hpc', ← site_end secondSite] at hraw
    exact hraw
  apply Stepper.runLocatedBlock_sound artifact fork secondSite.path
  · rw [henv]
    exact hcode
  · change middle.executionEnv.fork = fork
    rw [henv]
    exact hfork
  · rw [PairMultiplyLift.runLocatedBlock_eq_raw secondSite hsecond middle hpc']
    exact hraw'
  · exact hmidRun
  · rw [henv]
    exact hnp

#print axioms runInstrSeq_result_pc
#print axioms runInstrSeq_executionEnv
#print axioms gasSteps_splice
#print axioms gasSteps_twoPieces

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain
