import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentCap

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace CavityQuadGroup CavityPCTransport CavityFragmentChain

/-- The generic splice also exposes the preserved stack cap to its continuation. -/
noncomputable def gasSteps_splice_cap {artifact : ProgramArtifact} {fork : Fork}
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
      middle.stack.length < 1023 →
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
    (continuation relocated rfl henvMiddle hrunMiddle
      (hcap middle hprefix) hsuffixRelocated)


#print axioms gasSteps_splice_cap

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentCap
