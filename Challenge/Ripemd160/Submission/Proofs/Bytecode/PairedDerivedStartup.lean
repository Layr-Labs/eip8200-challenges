import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDerivedStartup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTrace DenseScheduleTemplate

def lowerWord : UInt256 := UInt256.ofNat 0xffffffff
def upperWord : UInt256 := UInt256.ofNat 0xffffffff00000000000000000000000000000000
def pairWord : UInt256 := UInt256.ofNat 0xffffffff000000000000000000000000ffffffff
def factorWord : UInt256 := UInt256.ofNat 0x0100000001

theorem upper_from_lower :
    UInt256.shiftLeft lowerWord (UInt256.ofNat 128) = upperWord := by decide

#print axioms upper_from_lower

theorem pair_from_lower : UInt256.lor lowerWord upperWord = pairWord := by decide

#print axioms pair_from_lower

def cacheTemplate : List Instr :=
  [.push ⟨4, by decide⟩ lowerWord,
   dup1, push1 (UInt256.ofNat 128), .op .SHL,
   dup1, .op (.Dup ⟨2, by decide⟩), .op .OR,
   .push ⟨5, by decide⟩ factorWord]

def loadTemplate (address : Nat) (_dup : Operation.DupOp) : List Instr :=
  [push1 (UInt256.ofNat address), .op .MLOAD, .op .JUMPDEST, .op .JUMPDEST,
   dup1, push1 (UInt256.ofNat 128), .op .SHL, .op .OR]

/-- Exact physical instructions 751..819 of the frozen 5324-byte candidate. -/
def template : List Instr :=
  cacheTemplate ++ loadTemplate 160 ⟨4, by decide⟩ ++
    loadTemplate 128 ⟨5, by decide⟩ ++ loadTemplate 96 ⟨6, by decide⟩ ++
    loadTemplate 64 ⟨7, by decide⟩ ++ loadTemplate 32 ⟨8, by decide⟩

/-- Arbitrary 256-bit words are explicitly normalized before duplicating lanes. -/
def packedHash (memory : ByteArray) (address : Nat) : UInt256 :=
  let value := UInt256.land lowerWord (MachineState.readWord memory address)
  UInt256.lor (UInt256.shiftLeft value (UInt256.ofNat 128)) value

def resultStack (memory : ByteArray) (rho : List UInt256) : List UInt256 :=
  [packedHash memory 32, packedHash memory 64, packedHash memory 96,
    packedHash memory 128, packedHash memory 160,
    factorWord, pairWord, upperWord, lowerWord] ++ rho

theorem active_preserved (current : UInt256) (address : Nat)
    (hcurrent : 23 ≤ current.toNat) (haddress : address ≤ 160) :
    UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32) = current := by
  have hwords : (address + 32 - 1) / 32 + 1 ≤ current.toNat := by omega
  simp only [MachineState.activeWordsAfter, if_neg (by decide : (32 : Nat) ≠ 0)]
  change UInt256.ofNat (max current.toNat ((address + 32 - 1) / 32 + 1)) = current
  rw [Nat.max_eq_left hwords]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat current).symm

theorem template_length : template.length = 48 := by
  norm_num [template, cacheTemplate, loadTemplate]

theorem template_bytes : (template.map Instr.size).sum = 68 := by
  norm_num [template, cacheTemplate, loadTemplate, push1, dup1, Instr.size]

/-- The five state words are already 32 bits wide, so masking them is identity.

Every write to those addresses is either a `PUSH4` literal or the compression
output, which the artifact masks with `lowerWord` in the instruction before the
store; `BlockContext.hash` records that.  The mask the window removes was
therefore redundant at every one of these addresses. -/
theorem run_template (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 1002) (hrun : s.halt = .Running)
    (hactive : 23 ≤ s.activeWords.toNat)
    (h32 : UInt256.land lowerWord (MachineState.readWord s.memory 32) =
      MachineState.readWord s.memory 32)
    (h64 : UInt256.land lowerWord (MachineState.readWord s.memory 64) =
      MachineState.readWord s.memory 64)
    (h96 : UInt256.land lowerWord (MachineState.readWord s.memory 96) =
      MachineState.readWord s.memory 96)
    (h128 : UInt256.land lowerWord (MachineState.readWord s.memory 128) =
      MachineState.readWord s.memory 128)
    (h160 : UInt256.land lowerWord (MachineState.readWord s.memory 160) =
      MachineState.readWord s.memory 160)
    :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc template, stack := resultStack s.memory rho} := by
  have hcap (n : Nat) (hn : n ≤ 11) : rho.length + n < 1024 := by omega
  have h0 : rho.length < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 160) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [template, cacheTemplate, loadTemplate, push1, dup1,
    packedHash, resultStack, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, hrun, hcap, h0, Nat.add_assoc,
    upper_from_lower, pair_from_lower,
    List.getElem?_cons_zero, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat, h32, h64, h96, h128, h160]
  rfl

#print axioms active_preserved
#print axioms template_length
#print axioms template_bytes
#print axioms run_template


open Challenge.EvmProof StackRoundTemplate

def frozenInstructions : List Instr :=
  [.push ⟨4, by decide⟩ (UInt256.ofNat 0xffffffff),
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHL,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .OR,
   .push ⟨5, by decide⟩ (UInt256.ofNat 0x0100000001),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0xa0),
   .op .MLOAD,
   .op .JUMPDEST,
   .op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHL,
   .op .OR,
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .MLOAD,
   .op .JUMPDEST,
   .op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHL,
   .op .OR,
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x60),
   .op .MLOAD,
   .op .JUMPDEST,
   .op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHL,
   .op .OR,
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x40),
   .op .MLOAD,
   .op .JUMPDEST,
   .op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHL,
   .op .OR,
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x20),
   .op .MLOAD,
   .op .JUMPDEST,
   .op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push ⟨1, by decide⟩ (UInt256.ofNat 0x80),
   .op .SHL,
   .op .OR]

theorem template_eq_frozenInstructions : template = frozenInstructions := by
  rfl

theorem template_advances :
    ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  rw [template_eq_frozenInstructions] at hmem
  simp only [frozenInstructions, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl (Or.inl (StraightLine.push _ _))
    | exact Or.inl (Or.inl StraightLine.and)
    | exact Or.inl (Or.inl StraightLine.or)
    | exact Or.inl (Or.inl StraightLine.shl)
    | exact Or.inl (Or.inl StraightLine.mload)
    | exact Or.inl (Or.inl (StraightLine.dup _))
    | exact Or.inl (Or.inr (Or.inr rfl))

theorem runLocatedBlock_template {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork template)
    (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (h32 : UInt256.land lowerWord (MachineState.readWord s.memory 32) =
      MachineState.readWord s.memory 32)
    (h64 : UInt256.land lowerWord (MachineState.readWord s.memory 64) =
      MachineState.readWord s.memory 64)
    (h96 : UInt256.land lowerWord (MachineState.readWord s.memory 96) =
      MachineState.readWord s.memory 96)
    (h128 : UInt256.land lowerWord (MachineState.readWord s.memory 128) =
      MachineState.readWord s.memory 128)
    (h160 : UInt256.land lowerWord (MachineState.readWord s.memory 160) =
      MachineState.readWord s.memory 160)
    :
    Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := rho} =
      some {s with pc := site.endPC, stack := resultStack s.memory rho} := by
  have hend : site.endPC = pcAfter site.startPC template := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  rw [DenseScheduleLift.runLocatedBlock_eq_raw site template_advances
    {s with pc := site.startPC, stack := rho} rfl]
  have h := run_template s site.startPC rho hstack hrun hactive h32 h64 h96 h128 h160
  rw [← hend] at h
  exact h

def gasSteps_template {artifact : ProgramArtifact} {fork : Fork}
    (site : GenericRoundSite artifact fork template)
    (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (h32 : UInt256.land lowerWord (MachineState.readWord s.memory 32) =
      MachineState.readWord s.memory 32)
    (h64 : UInt256.land lowerWord (MachineState.readWord s.memory 64) =
      MachineState.readWord s.memory 64)
    (h96 : UInt256.land lowerWord (MachineState.readWord s.memory 96) =
      MachineState.readWord s.memory 96)
    (h128 : UInt256.land lowerWord (MachineState.readWord s.memory 128) =
      MachineState.readWord s.memory 128)
    (h160 : UInt256.land lowerWord (MachineState.readWord s.memory 160) =
      MachineState.readWord s.memory 160)
    :
    GasSteps {s with pc := site.startPC, stack := rho}
      {s with pc := site.endPC, stack := resultStack s.memory rho} := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_template site s rho hstack hrun hactive h32 h64 h96 h128 h160
  · exact hrun
  · exact hnp

#print axioms template_eq_frozenInstructions
#print axioms template_advances
#print axioms runLocatedBlock_template
#print axioms gasSteps_template


theorem template_exactBytes : assembleBytes template =
  [0x63, 0xff, 0xff, 0xff, 0xff, 0x80, 0x60, 0x80, 0x1b, 0x80, 0x82, 0x17,
  0x64, 0x01, 0x00, 0x00, 0x00, 0x01, 0x60, 0xa0, 0x51, 0x5b, 0x5b, 0x80,
  0x60, 0x80, 0x1b, 0x17, 0x60, 0x80, 0x51, 0x5b, 0x5b, 0x80, 0x60, 0x80,
  0x1b, 0x17, 0x60, 0x60, 0x51, 0x5b, 0x5b, 0x80, 0x60, 0x80, 0x1b, 0x17,
  0x60, 0x40, 0x51, 0x5b, 0x5b, 0x80, 0x60, 0x80, 0x1b, 0x17, 0x60, 0x20,
  0x51, 0x5b, 0x5b, 0x80, 0x60, 0x80, 0x1b, 0x17] := by decide

#print axioms template_exactBytes

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDerivedStartup
