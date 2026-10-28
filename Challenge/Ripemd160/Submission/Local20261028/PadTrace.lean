import Challenge.Ripemd160.Submission.Local20261028.ModFoldLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionLift
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace

theorem executionEnv {code : List Instr} {s t : State}
    (h : runInstrSeq code s = some t) : t.executionEnv = s.executionEnv := by
  induction code generalizing s with
  | nil => simp only [runInstrSeq, Option.some.injEq] at h; subst t; rfl
  | cons i rest ih =>
    cases hn : DataStepper.runInstr i s with
    | none => simp [runInstrSeq, hn] at h
    | some u =>
      have he := DataStepper.runInstr_executionEnv hn
      cases rest with
      | nil => simp only [runInstrSeq, hn, Option.some.injEq] at h; subst t; exact he
      | cons j tail =>
        cases hh : u.halt <;> simp [runInstrSeq, hn, hh] at h
        exact (ih h).trans he

theorem split {a b : List Instr} {s t : State} (hb : b ≠ []) (hs : s.halt = .Running)
    (h : runInstrSeq (a++b) s = some t) :
    ∃ u, runInstrSeq a s = some u ∧ u.halt = .Running ∧ runInstrSeq b u = some t := by
  induction a generalizing s with
  | nil => exact ⟨s,rfl,hs,h⟩
  | cons i rest ih =>
    cases hn : DataStepper.runInstr i s with
    | none => simp [runInstrSeq, hn] at h
    | some u =>
      cases b with
      | nil => contradiction
      | cons j tail =>
        cases rest with
        | nil =>
          cases hh : u.halt <;> simp [runInstrSeq, hn, hh] at h
          exact ⟨u, by simp [runInstrSeq,hn], hh, h⟩
        | cons k rest =>
          cases hh : u.halt <;> simp only [List.cons_append, runInstrSeq, hn, hh] at h
          all_goals try contradiction
          obtain ⟨v,hv,hvr,hb⟩ := ih hh h
          exact ⟨v, by simpa [runInstrSeq,hn,hh] using hv, hvr, hb⟩

theorem jump_pc {target : UInt256} {s t : State}
    (h : runInstrSeq [.push ⟨2,by decide⟩ target, .op .JUMP] s = some t) : t.pc = target := by
  by_cases hcap : s.stack.length < 1024
  · by_cases hcap2 : s.stack.length+1 < 1024
    · by_cases hv : Decode.isValidJumpDest s.executionEnv.code target.toNat = true
      · cases hh : s.halt <;> simp [runInstrSeq,DataStepper.runInstr,hcap,hcap2,hv,hh] at h
        cases h; rfl
      · simp [runInstrSeq,DataStepper.runInstr,hcap,hcap2,hv] at h
        cases hh : s.halt <;> simp [hh] at h
    · simp [runInstrSeq,DataStepper.runInstr,hcap,hcap2] at h
      cases hh : s.halt <;> simp [hh] at h
  · simp [runInstrSeq,DataStepper.runInstr,hcap] at h

theorem ends_jump_pc {before : List Instr} {target : UInt256} {s t : State}
    (hs : s.halt = .Running)
    (h : runInstrSeq (before ++ [.push ⟨2,by decide⟩ target, .op .JUMP]) s = some t) :
    t.pc = target := by
  obtain ⟨u,_,_,hu⟩ := split (by simp) hs h
  exact jump_pc hu

def Advances (i : Instr) : Prop := RecognitionLift.Advances i ∨ i = .op .MULMOD
def advancesCheck : Instr → Bool
  | .op .MULMOD => true
  | i => RecognitionLift.advancesCheck i

theorem advancesCheck_sound (i : Instr) (h : advancesCheck i = true) : Advances i := by
  by_cases hm : i = .op .MULMOD
  · exact Or.inr hm
  left
  apply RecognitionLift.advancesCheck_sound
  cases i with
  | push width value => exact h
  | op op => cases op <;> simp_all [advancesCheck]

theorem runInstr_pc {i : Instr} {s t : State} (hf : Advances i)
    (h : DataStepper.runInstr i s = some t) : t.pc = s.pc + UInt256.ofNat i.size := by
  rcases hf with hf | hf
  · exact RecognitionLift.runInstr_pc_extra hf h
  · subst i; exact ModFoldLift.runInstr_pc_mulmod h

def gasSteps_of_raw {artifact : DataProgramArtifact} {fork : Fork}
    {code : List Instr} (site : GenericRoundSite artifact fork code)
    (s t : State) (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hpc : s.pc = site.startPC)
    (hform : code.dropLast.all advancesCheck = true)
    (hresult : runInstrSeq code s = some t) : GasSteps s t := by
  apply DataStepper.runLocatedBlock_sound artifact fork site.path hcode hfork
  · have hl := runLocatedBlock_eq_raw_terminal_sites site.sites code
      site.instruction_eq site.contiguous s (by rw [site.head_eq]; exact congrArg some hpc.symm) (by
        intro located hmem u v hr
        apply runInstr_pc (advancesCheck_sound _ ?_) hr
        apply List.all_eq_true.mp hform
        have hm : located.located.instruction ∈
            site.sites.dropLast.map (fun item => item.located.instruction) := List.mem_map_of_mem hmem
        rw [List.map_dropLast, site.instruction_eq] at hm
        exact hm)
    change DataStepper.runLocatedBlock (LocatedSite.path site.sites) s = some t
    rw [hl]
    exact hresult
  · exact hrun
  · exact hnp
#print axioms executionEnv
#print axioms split
#print axioms ends_jump_pc
#print axioms gasSteps_of_raw
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadTrace
