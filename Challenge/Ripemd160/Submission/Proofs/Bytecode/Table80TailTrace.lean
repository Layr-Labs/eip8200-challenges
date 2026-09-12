import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Tail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
set_option warningAsError true
set_option maxRecDepth 30000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Tail
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace Paired80WordRound
theorem tail_prefix_advances :
    ∀ instruction ∈ prefixTemplate, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [prefixTemplate, template, List.dropLast_cons_cons, List.dropLast_singleton, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl (Or.inl (StraightLine.push _ _))
    | exact Or.inl (Or.inl StraightLine.add)
    | exact Or.inl (Or.inl StraightLine.and)
    | exact Or.inl (Or.inl StraightLine.shr)
    | exact Or.inl (Or.inl StraightLine.mload)
    | exact Or.inl (Or.inl StraightLine.pop)
    | exact Or.inl (Or.inl (StraightLine.dup _))
    | exact Or.inr (Or.inl rfl)

theorem runLocatedBlock_tail_prefix {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork prefixTemplate)
    (s : State) (ret : UInt256) (q : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := entryStack q ret rho} =
      some {s with pc := site.endPC, stack := ret :: rho, memory := cleanedResultMemory s.memory q} := by
  have hend : site.endPC = pcAfter site.startPC prefixTemplate := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [DenseScheduleLift.runLocatedBlock_eq_raw site tail_prefix_advances
    {s with pc := site.startPC, stack := entryStack q ret rho} rfl]
  have h := run_prefix s site.startPC ret q rho hstack hrun hactive
  rw [← hend] at h
  exact h

structure TailSite (artifact : ProgramArtifact) (fork : Fork) where
  prefixSite : GenericRoundSite artifact fork prefixTemplate
  jump : LocatedSite artifact fork
  jump_instr : jump.located.instruction = .op .JUMP
  jump_pc : jump.pc = prefixSite.endPC

def TailSite.path {artifact : ProgramArtifact} {fork : Fork}
    (site : TailSite artifact fork) : List (Stepper.Located artifact fork) :=
  site.prefixSite.path ++ [site.jump.located]

theorem runLocatedBlock_tail {artifact : ProgramArtifact} {fork : Fork}
    (site : TailSite artifact fork) (s : State) (ret : UInt256) (q : WordLane)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    Stepper.runLocatedBlock site.path
      {s with pc := site.prefixSite.startPC, stack := entryStack q ret rho} =
      some {s with pc := ret, stack := rho, memory := cleanedResultMemory s.memory q} := by
  apply Stepper.runLocatedBlock_append site.prefixSite.path [site.jump.located]
    _ {s with
      pc := site.prefixSite.endPC
      stack := ret :: rho
      memory := cleanedResultMemory s.memory q}
  · exact runLocatedBlock_tail_prefix site.prefixSite s ret q rho hstack hrun hactive
  · exact hrun
  · have h := SharedCallTrace.runLocated_jump site.jump site.jump_instr
      {s with memory := cleanedResultMemory s.memory q} ret rho (by omega) hvalid
    rw [site.jump_pc] at h
    simp only [Stepper.runLocatedBlock, h]

def gasSteps_tail {artifact : ProgramArtifact} {fork : Fork}
    (site : TailSite artifact fork) (s : State) (ret : UInt256) (q : WordLane)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.prefixSite.startPC, stack := entryStack q ret rho}
      {s with pc := ret, stack := rho, memory := cleanedResultMemory s.memory q} := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_tail site s ret q rho hstack hrun hactive hvalid
  · exact hrun
  · exact hnp

#print axioms gasSteps_tail
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Tail
