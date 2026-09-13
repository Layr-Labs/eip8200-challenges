import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentLoopLift
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace

def Advances (instruction : Instr) : Prop :=
  PadLift.Advances instruction ∨ instruction = .op .ISZERO

theorem runInstr_pc_extra {instruction : Instr} {s t : State}
    (hform : Advances instruction) (hresult : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  rcases hform with hold | hz
  · exact PadLift.runInstr_pc_extra hold hresult
  · subst instruction
    by_cases hcap : s.stack.length < 1024
    · simp only [Stepper.runInstr, if_pos hcap] at hresult
      cases hs : s.stack with
      | nil => simp [hs] at hresult
      | cons a rest =>
        simp only [hs] at hresult
        cases hresult
        rfl
    · simp [Stepper.runInstr, hcap] at hresult

def advancesCheck : Instr → Bool
  | .op .ISZERO => true
  | i => PadLift.advancesCheck i

theorem advancesCheck_sound (instruction : Instr)
    (h : advancesCheck instruction = true) : Advances instruction := by
  cases instruction with
  | push width value => exact Or.inl (PadLift.advancesCheck_sound _ h)
  | op operation =>
    cases operation <;> first
      | exact Or.inr rfl
      | exact Or.inl (PadLift.advancesCheck_sound _ h)
      | (rename_i inner; cases inner <;> first
          | exact Or.inr rfl
          | exact Or.inl (PadLift.advancesCheck_sound _ h))

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
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentLoopLift
