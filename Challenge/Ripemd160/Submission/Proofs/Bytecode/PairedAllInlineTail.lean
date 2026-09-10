import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTail

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineTail

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace PairedTailTrace

/-- The same arbitrary logical tail frame, in the all-inline final physical order. -/
def entryStack (q : PairedTailTrace.Frame) (ret : UInt256) (rho : List UInt256) : List UInt256 :=
  [q.d, q.b, q.c, q.a, q.e, q.unused5, q.unused6, q.unused3, q.lower, ret] ++ rho

/-- Exact frozen5357 window5196..5277: all results are computed before any write. -/
def template : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .SHR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 64),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .SHR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 96),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .SHR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .SHR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 160),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .SHR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 32),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 160),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 96),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 64),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 32),
   .op .MSTORE,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .JUMP]

theorem tail_template_length : template.length = 70 := by
  norm_num [template]

#print axioms tail_template_length

theorem tail_template_bytes : (template.map Instr.size).sum = 85 := by
  norm_num [template, Instr.size]

#print axioms tail_template_bytes

theorem run_tail_template (s : State) (pc ret : UInt256) (q : PairedTailTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstrSeq template {s with pc := pc, stack := entryStack q ret rho} =
      some {s with pc := ret, stack := rho, memory := resultMemory s.memory q} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 160) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := PairedStartupTrace.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, entryStack, combine,
    result0, result1, result2, result3, result4, resultMemory, writeWord,
    runInstrSeq, Challenge.EvmProof.Stepper.runInstr, UInt256.succ,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero,
    State.activeWordsAfterUInt256, hactiveAt, hvalid,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rfl

#print axioms run_tail_template

open Challenge.EvmProof StackRoundTemplate

def prefixTemplate : List Instr :=
  [.op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .SHR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 64),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op .AND,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .SHR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 96),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨10, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .SHR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op .AND,
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .SHR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 160),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨12, by decide⟩),
   .op .AND,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .SHR,
   .op .ADD,
   .push ⟨1, by decide⟩ (UInt256.ofNat 32),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨13, by decide⟩),
   .op .AND,
   .push ⟨1, by decide⟩ (UInt256.ofNat 160),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 128),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 96),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 64),
   .op .MSTORE,
   .push ⟨1, by decide⟩ (UInt256.ofNat 32),
   .op .MSTORE,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP]

theorem tail_prefix_append_jump : prefixTemplate ++ [.op .JUMP] = template := by
  rfl

#print axioms tail_prefix_append_jump

theorem run_tail_prefix (s : State) (pc ret : UInt256) (q : PairedTailTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat) :
    runInstrSeq prefixTemplate {s with pc := pc, stack := entryStack q ret rho} =
      some {s with
        pc := pcAfter pc prefixTemplate
        stack := ret :: rho
        memory := resultMemory s.memory q} := by
  have hcap (n : Nat) (hn : n ≤ 20) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 160) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := PairedStartupTrace.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [prefixTemplate, entryStack, combine,
    result0, result1, result2, result3, result4, resultMemory, writeWord,
    runInstrSeq, Stepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    hrun, hcap, Nat.add_assoc, List.getElem?_cons_zero,
    State.activeWordsAfterUInt256, hactiveAt, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact ⟨rfl, rfl⟩

#print axioms run_tail_prefix

theorem tail_prefix_advances :
    ∀ instruction ∈ prefixTemplate, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [prefixTemplate, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl (Or.inl (StraightLine.push _ _))
    | exact Or.inl (Or.inl StraightLine.add)
    | exact Or.inl (Or.inl StraightLine.and)
    | exact Or.inl (Or.inl StraightLine.shr)
    | exact Or.inl (Or.inl StraightLine.mload)
    | exact Or.inl (Or.inl StraightLine.pop)
    | exact Or.inl (Or.inl (StraightLine.dup _))
    | exact Or.inr (Or.inl rfl)

#print axioms tail_prefix_advances

theorem runLocatedBlock_tail_prefix {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork prefixTemplate)
    (s : State) (ret : UInt256) (q : PairedTailTrace.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat) :
    Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := entryStack q ret rho} =
      some {s with pc := site.endPC, stack := ret :: rho, memory := resultMemory s.memory q} := by
  have hend : site.endPC = pcAfter site.startPC prefixTemplate := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [DenseScheduleLift.runLocatedBlock_eq_raw site tail_prefix_advances
    {s with pc := site.startPC, stack := entryStack q ret rho} rfl]
  have h := run_tail_prefix s site.startPC ret q rho hstack hrun hactive
  rw [← hend] at h
  exact h

#print axioms runLocatedBlock_tail_prefix

structure TailSite (artifact : ProgramArtifact) (fork : Fork) where
  prefixSite : GenericRoundSite artifact fork prefixTemplate
  jump : LocatedSite artifact fork
  jump_instr : jump.located.instruction = .op .JUMP
  jump_pc : jump.pc = prefixSite.endPC

def TailSite.path {artifact : ProgramArtifact} {fork : Fork}
    (site : TailSite artifact fork) : List (Stepper.Located artifact fork) :=
  site.prefixSite.path ++ [site.jump.located]

theorem runLocatedBlock_tail {artifact : ProgramArtifact} {fork : Fork}
    (site : TailSite artifact fork) (s : State) (ret : UInt256) (q : PairedTailTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    Stepper.runLocatedBlock site.path
      {s with pc := site.prefixSite.startPC, stack := entryStack q ret rho} =
      some {s with pc := ret, stack := rho, memory := resultMemory s.memory q} := by
  apply Stepper.runLocatedBlock_append site.prefixSite.path [site.jump.located]
    _ {s with
      pc := site.prefixSite.endPC
      stack := ret :: rho
      memory := resultMemory s.memory q}
  · exact runLocatedBlock_tail_prefix site.prefixSite s ret q rho hstack hrun hactive
  · exact hrun
  · have h := SharedCallTrace.runLocated_jump site.jump site.jump_instr
      {s with memory := resultMemory s.memory q} ret rho (by omega) hvalid
    rw [site.jump_pc] at h
    simp only [Stepper.runLocatedBlock, h]

#print axioms runLocatedBlock_tail

def gasSteps_tail {artifact : ProgramArtifact} {fork : Fork}
    (site : TailSite artifact fork) (s : State) (ret : UInt256) (q : PairedTailTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.prefixSite.startPC, stack := entryStack q ret rho}
      {s with pc := ret, stack := rho, memory := resultMemory s.memory q} := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_tail site s ret q rho hstack hrun hactive hvalid
  · exact hrun
  · exact hnp

#print axioms gasSteps_tail

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineTail
