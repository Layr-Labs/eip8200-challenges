import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentLoopLift
set_option warningAsError true
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace

def Advances (instruction : Instr) : Prop :=
  PersistentLoopLift.Advances instruction ∨ instruction = .op .CALLDATALOAD ∨
    instruction = .op .DIV ∨ instruction = .op .MOD ∨ instruction = .op .LT ∨
    instruction = .op .SUB ∨ instruction = .op .CODECOPY ∨ instruction = .op .MSIZE

theorem runInstr_pc_extra {instruction : Instr} {s t : State}
    (hform : Advances instruction) (hresult : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  rcases hform with hold | hcl | hd | hm | hl | hs | hc | hms
  · exact PersistentLoopLift.runInstr_pc_extra hold hresult
  all_goals subst instruction
  all_goals by_cases hcap : s.stack.length < 1024
  all_goals try { simp [Stepper.runInstr, hcap] at hresult }
  all_goals simp only [Stepper.runInstr, if_pos hcap] at hresult
  all_goals try { cases hresult; rfl }
  all_goals cases hs : s.stack with
  | nil => simp [hs] at hresult
  | cons a rest =>
    simp only [hs] at hresult
    first
    | (cases hresult; rfl)
    | cases ht : rest with
      | nil => simp [ht] at hresult
      | cons b rest2 =>
        simp only [ht] at hresult
        first
        | (cases hresult; rfl)
        | cases hu : rest2 with
          | nil => simp [hu] at hresult
          | cons c rest3 =>
            simp only [hu] at hresult
            cases hresult
            rfl

def advancesCheck : Instr → Bool
  | .op .CALLDATALOAD | .op .DIV | .op .MOD | .op .LT |
    .op .SUB | .op .CODECOPY | .op .MSIZE => true
  | i => PersistentLoopLift.advancesCheck i

theorem advancesCheck_sound (instruction : Instr)
    (h : advancesCheck instruction = true) : Advances instruction := by
  cases instruction with
  | push width value => exact Or.inl (PersistentLoopLift.advancesCheck_sound _ h)
  | op operation =>
    cases operation <;> first
      | (simp only [Advances]; tauto)
      | exact Or.inl (PersistentLoopLift.advancesCheck_sound _ h)
      | (rename_i inner; cases inner <;> first
          | (simp only [Advances]; tauto)
          | exact Or.inl (PersistentLoopLift.advancesCheck_sound _ h))

theorem advancesAll_sound (code : List Instr) (h : code.all advancesCheck = true) :
    ∀ instruction ∈ code, Advances instruction := by
  intro instruction hi
  exact advancesCheck_sound instruction ((List.all_eq_true.mp h) instruction hi)

def gasSteps_of_raw {artifact : ProgramArtifact} {fork : Fork}
    {code : List Instr} (site : GenericRoundSite artifact fork code)
    (s t : State) (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hpc : s.pc = site.startPC)
    (hform : ∀ instruction ∈ code.dropLast, Advances instruction)
    (hresult : runInstrSeq code s = some t) : GasSteps s t := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path hcode hfork
  · have hl := runLocatedBlock_eq_raw_terminal_sites site.sites code
      site.instruction_eq site.contiguous s (by rw [site.head_eq]; exact congrArg some hpc.symm) (by
        intro located hmem u v hr
        apply runInstr_pc_extra (hform _ ?_) hr
        have hm : located.located.instruction ∈
            site.sites.dropLast.map (fun item => item.located.instruction) := List.mem_map_of_mem hmem
        rw [List.map_dropLast, site.instruction_eq] at hm
        exact hm)
    change Stepper.runLocatedBlock (LocatedSite.path site.sites) s = some t
    rw [hl]
    exact hresult
  · exact hrun
  · exact hnp
#print axioms gasSteps_of_raw
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
