import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedSpreadProduct
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDivMaskCache

set_option warningAsError true

/-! A startup specialization for the five hash words already normalized by the
compression invariant. The five explicit mask identities are required; no
unconditional equivalence for arbitrary memory is asserted. Each word is
duplicated into its upper lane by multiplication by `2^128 + 1`. The factor
is derived from the existing pair and lower masks by exact division, and
the five memory addresses use their minimal one-byte immediates. The invariant-based omission was informed by
ercumentyildirim's public, unpromoted submission
e63fc232361e8c72985b139d09c221ac4da6f3a1. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedNormalizedStartup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof StackRoundTrace DenseScheduleTemplate PairedDerivedStartup

/-- The three lane constants, without the round factor that used to follow. -/
def headTemplate : List Instr :=
  [.push ⟨4, by decide⟩ lowerWord,
   dup1, push1 (UInt256.ofNat 128), .op .SHL,
   dup1, .op (.Dup ⟨2, by decide⟩), .op .OR]

def loadTemplate (address : Nat) (dup : Operation.DupOp) : List Instr :=
  [.push ⟨1, by decide⟩ (UInt256.ofNat address), .op .MLOAD, .op (.Dup dup), .op .MUL]

def template : List Instr :=
  headTemplate ++ [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .DIV] ++
    loadTemplate 160 ⟨1, by decide⟩ ++ loadTemplate 128 ⟨2, by decide⟩ ++
    loadTemplate 96 ⟨3, by decide⟩ ++ loadTemplate 64 ⟨4, by decide⟩ ++
    loadTemplate 32 ⟨5, by decide⟩ ++
    [.push ⟨5, by decide⟩ factorWord, .op (.Swap ⟨5, by decide⟩), .op .POP]

theorem mask_identity_ofUInt32 (x : UInt32) :
    UInt256.land lowerWord (Word.ofUInt32 x) = Word.ofUInt32 x := by
  have h := Word.mask32_ofUInt32 x
  simp only [Word.mask32] at h
  rw [Word.land_comm, lowerWord]
  exact h

theorem template_length : template.length = 33 := by
  norm_num [template, headTemplate, loadTemplate]

theorem template_bytes : (template.map Instr.size).sum = 48 := by
  norm_num [template, headTemplate, loadTemplate, push1, dup1, Instr.size]

theorem load_bytes (address : Nat) (dup : Operation.DupOp) :
    ((loadTemplate address dup).map Instr.size).sum = 5 := by
  norm_num [loadTemplate, Instr.size]

theorem spread_div : pairWord / lowerWord = PairedSpreadProduct.spreadFactor := by decide

#print axioms spread_div

private theorem add_eq_hAdd (a b : UInt256) : UInt256.add a b = a + b := rfl

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
      MachineState.readWord s.memory 160) :
    runInstrSeq template {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc template, stack := resultStack s.memory rho} := by
  have hcap (n : Nat) (hn : n ≤ 11) : rho.length + n < 1024 := by omega
  have h0 : rho.length < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 160) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) =
        s.activeWords := active_preserved s.activeWords address hactive haddress
  have hspread (address : Nat)
      (h : UInt256.land lowerWord (MachineState.readWord s.memory address) =
        MachineState.readWord s.memory address) :
      PairedSpreadProduct.spreadFactor * MachineState.readWord s.memory address
        = packedHash s.memory address := by
    show UInt256.mul PairedSpreadProduct.spreadFactor
      (MachineState.readWord s.memory address) = _
    rw [PairedSpreadProduct.spread_mul _ h]
    unfold packedHash
    rw [h]
  have m32 := hspread 32 h32
  have m64 := hspread 64 h64
  have m96 := hspread 96 h96
  have m128 := hspread 128 h128
  have m160 := hspread 160 h160
  simp (discharger := omega) [template, headTemplate, loadTemplate, push1, dup1,
    resultStack, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, hrun, hcap, h0, Nat.add_assoc, add_eq_hAdd,
    upper_from_lower, pair_from_lower, spread_div,
    List.getElem?_cons_zero, List.exchange, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat, m32, m64, m96, m128, m160]
  all_goals rfl

open Challenge.EvmProof StackRoundTemplate

theorem template_advances :
    ∀ instruction ∈ template, DenseScheduleLift.Advances instruction ∨ instruction = .op .DIV := by
  intro instruction hmem
  simp only [template, headTemplate, loadTemplate,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inr rfl
    | apply Or.inl
      first
      | exact Or.inl (Or.inl (StraightLine.push _ _))
      | exact Or.inl (Or.inl StraightLine.or)
      | exact Or.inl (Or.inl StraightLine.shl)
      | exact Or.inl (Or.inl StraightLine.mload)
      | exact Or.inl (Or.inl StraightLine.pop)
      | exact Or.inl (Or.inl (StraightLine.dup _))
      | exact Or.inl (Or.inl (StraightLine.swap _))
      | exact Or.inr (Or.inr rfl)


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
      MachineState.readWord s.memory 160) :
    Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := rho} =
      some {s with pc := site.endPC, stack := resultStack s.memory rho} := by
  have hend : site.endPC = pcAfter site.startPC template := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  have hraw : Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := rho} =
      runInstrSeq template {s with pc := site.startPC, stack := rho} := by
    apply runLocatedBlock_eq_runInstrSeq_site site _ rfl
    intro located hmem u v hresult
    have hi : located.located.instruction ∈ template := by
      rw [← site.instruction_eq]
      exact List.mem_map_of_mem hmem
    rcases template_advances located.located.instruction hi with hnormal | hdiv
    · exact DenseScheduleLift.runInstr_pc_of_advances hnormal hresult
    · rw [hdiv] at hresult
      simpa [hdiv] using PairedDivMaskCache.runInstr_pc_div hresult
  rw [hraw]
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
      MachineState.readWord s.memory 160) :
    GasSteps {s with pc := site.startPC, stack := rho}
      {s with pc := site.endPC, stack := resultStack s.memory rho} := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact runLocatedBlock_template site s rho hstack hrun hactive h32 h64 h96 h128 h160
  · exact hrun
  · exact hnp

theorem template_exactBytes : assembleBytes template =
  [0x63, 0xff, 0xff, 0xff, 0xff, 0x80, 0x60, 0x80, 0x1b, 0x80, 0x82, 0x17, 0x82, 0x81, 0x04, 0x60, 0xa0, 0x51, 0x81, 0x02, 0x60, 0x80, 0x51, 0x82, 0x02, 0x60, 0x60, 0x51, 0x83, 0x02, 0x60, 0x40, 0x51, 0x84, 0x02, 0x60, 0x20, 0x51, 0x85, 0x02, 0x64, 0x01, 0x00, 0x00, 0x00, 0x01, 0x95, 0x50] := by decide

#print axioms mask_identity_ofUInt32
#print axioms template_length
#print axioms template_bytes
#print axioms load_bytes
#print axioms run_template
#print axioms template_advances
#print axioms runLocatedBlock_template
#print axioms gasSteps_template
#print axioms template_exactBytes

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedNormalizedStartup
