import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

/-! Straight-line lift for core templates that additionally contain `MOD` (the compact MOD fold). -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ModFoldLift

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace

theorem runInstr_pc_mod {s t : State}
    (hresult : DataStepper.runInstr (.op .MOD) s = some t) :
    t.pc = s.pc + UInt256.ofNat (Instr.op .MOD).size := by
  by_cases hcap : s.stack.length < 1024
  · rw [DataStepper.runInstr, if_pos hcap] at hresult
    cases hs : s.stack with
    | nil => simp [hs] at hresult
    | cons a tail =>
        cases ht : tail with
        | nil => simp [hs, ht] at hresult
        | cons b rest =>
            simp [hs, ht] at hresult
            subst t
            rfl
  · simp [DataStepper.runInstr, hcap] at hresult

theorem runInstr_pc_mulmod {s t : State}
    (hresult : DataStepper.runInstr (.op .MULMOD) s = some t) :
    t.pc = s.pc + UInt256.ofNat (Instr.op .MULMOD).size := by
  by_cases hcap : s.stack.length < 1024
  · rw [DataStepper.runInstr, if_pos hcap] at hresult
    cases hs : s.stack with
    | nil => simp [hs] at hresult
    | cons a tail =>
      cases ht : tail with
      | nil => simp [hs, ht] at hresult
      | cons b tail =>
        cases hn : tail with
        | nil => simp [hs, ht, hn] at hresult
        | cons n rest =>
          simp [hs, ht, hn] at hresult
          subst t
          rfl
  · simp [DataStepper.runInstr, hcap] at hresult

def Advances (instruction : Instr) : Prop :=
  DenseScheduleLift.Advances instruction ∨ instruction = .op .MOD ∨ instruction = .op .MULMOD

theorem runInstr_pc_of_advances {instruction : Instr} {s t : State}
    (hform : Advances instruction)
    (hresult : DataStepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  rcases hform with hdense | hmod | hmulmod
  · exact DenseScheduleLift.runInstr_pc_of_advances hdense hresult
  · subst instruction
    exact runInstr_pc_mod hresult
  · subst instruction
    exact runInstr_pc_mulmod hresult

def advancesCheck : Instr → Bool
  | .op .MOD | .op .MULMOD => true
  | instruction => Table80SiteCommon.coreAdvancesCheck instruction

theorem advancesCheck_sound (instruction : Instr)
    (h : advancesCheck instruction = true) : Advances instruction := by
  by_cases hmod : instruction = .op .MOD
  · exact Or.inr (Or.inl hmod)
  by_cases hmulmod : instruction = .op .MULMOD
  · exact Or.inr (Or.inr hmulmod)
  left
  apply Table80SiteCommon.coreAdvancesCheck_sound
  cases instruction with
  | push width value => simpa [advancesCheck] using h
  | op operation => cases operation <;> simp_all [advancesCheck]

theorem advancesAll_sound (code : List Instr)
    (h : code.all advancesCheck = true) :
    ∀ instruction ∈ code, Advances instruction := by
  intro instruction hmem
  exact advancesCheck_sound instruction ((List.all_eq_true.mp h) instruction hmem)

theorem runLocatedBlock_eq_raw {artifact : DataProgramArtifact} {fork : Fork}
    {template : List Instr} (site : GenericRoundSite artifact fork template)
    (hform : ∀ instruction ∈ template, Advances instruction)
    (s : State) (hpc : s.pc = site.startPC) :
    DataStepper.runLocatedBlock site.path s = StackRoundTrace.runInstrSeq template s := by
  apply StackRoundTrace.runLocatedBlock_eq_runInstrSeq_site site s hpc
  intro located hmem u v hresult
  apply runInstr_pc_of_advances _ hresult
  apply hform
  rw [← site.instruction_eq]
  exact List.mem_map_of_mem hmem

def gasSteps_of_raw {artifact : DataProgramArtifact} {fork : Fork}
    {template : List Instr} (site : GenericRoundSite artifact fork template)
    (s t : State)
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hpc : s.pc = site.startPC)
    (hform : ∀ instruction ∈ template, Advances instruction)
    (hresult : StackRoundTrace.runInstrSeq template s = some t) :
    GasSteps s t := by
  apply DataStepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · rw [runLocatedBlock_eq_raw site hform s hpc]
    exact hresult
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ModFoldLift
