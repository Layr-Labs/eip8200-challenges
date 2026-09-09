import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDerivedStartup

set_option warningAsError true

/-! A startup specialization for the five hash words already normalized by the
compression invariant. The five explicit mask identities are required; no
unconditional equivalence for arbitrary memory is asserted. Widening each
address push preserves every ten-byte load window without padding operations.
The invariant-based omission was informed by ercumentyildirim's public,
unpromoted submission e63fc232361e8c72985b139d09c221ac4da6f3a1. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedNormalizedStartup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof StackRoundTrace DenseScheduleTemplate PairedDerivedStartup

def loadTemplate (address : Nat) : List Instr :=
  [.push ⟨3, by decide⟩ (UInt256.ofNat address), .op .MLOAD,
   dup1, push1 (UInt256.ofNat 128), .op .SHL, .op .OR]

def template : List Instr :=
  cacheTemplate ++ loadTemplate 160 ++ loadTemplate 128 ++
    loadTemplate 96 ++ loadTemplate 64 ++ loadTemplate 32

theorem mask_identity_ofUInt32 (x : UInt32) :
    UInt256.land lowerWord (Word.ofUInt32 x) = Word.ofUInt32 x := by
  have h := Word.mask32_ofUInt32 x
  simp only [Word.mask32] at h
  rw [Word.land_comm, lowerWord]
  exact h

theorem template_length : template.length = 38 := by
  norm_num [template, cacheTemplate, loadTemplate]

theorem template_bytes : (template.map Instr.size).sum = 68 := by
  norm_num [template, cacheTemplate, loadTemplate, push1, dup1, Instr.size]

theorem load_bytes (address : Nat) :
    ((loadTemplate address).map Instr.size).sum = 10 := by
  norm_num [loadTemplate, push1, dup1, Instr.size]

theorem template_gas_saving :
    staticGas template + 30 = staticGas PairedDerivedStartup.template := by
  norm_num [staticGas, template, PairedDerivedStartup.template,
    cacheTemplate, loadTemplate, PairedDerivedStartup.loadTemplate,
    push1, dup1, Meter.instrStaticCost, Gas.baseCost]

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
  simp (discharger := omega) [template, cacheTemplate, loadTemplate, push1, dup1,
    packedHash, resultStack, runInstrSeq, Challenge.EvmProof.Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, hrun, hcap, h0, Nat.add_assoc,
    upper_from_lower, pair_from_lower,
    List.getElem?_cons_zero, State.activeWordsAfterUInt256, hactiveAt,
    Challenge.EvmProof.Word.word_toNat_ofNat, h32, h64, h96, h128, h160]
  rfl

open Challenge.EvmProof StackRoundTemplate

theorem template_advances :
    ∀ instruction ∈ template, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [template, cacheTemplate, loadTemplate,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl (Or.inl (StraightLine.push _ _))
    | exact Or.inl (Or.inl StraightLine.or)
    | exact Or.inl (Or.inl StraightLine.shl)
    | exact Or.inl (Or.inl StraightLine.mload)
    | exact Or.inl (Or.inl (StraightLine.dup _))

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
  [0x63, 0xff, 0xff, 0xff, 0xff, 0x80, 0x60, 0x80, 0x1b, 0x80, 0x82, 0x17,
   0x64, 0x01, 0x00, 0x00, 0x00, 0x01,
   0x62, 0x00, 0x00, 0xa0, 0x51, 0x80, 0x60, 0x80, 0x1b, 0x17,
   0x62, 0x00, 0x00, 0x80, 0x51, 0x80, 0x60, 0x80, 0x1b, 0x17,
   0x62, 0x00, 0x00, 0x60, 0x51, 0x80, 0x60, 0x80, 0x1b, 0x17,
   0x62, 0x00, 0x00, 0x40, 0x51, 0x80, 0x60, 0x80, 0x1b, 0x17,
   0x62, 0x00, 0x00, 0x20, 0x51, 0x80, 0x60, 0x80, 0x1b, 0x17] := by decide

#print axioms mask_identity_ofUInt32
#print axioms template_length
#print axioms template_bytes
#print axioms load_bytes
#print axioms template_gas_saving
#print axioms run_template
#print axioms template_advances
#print axioms runLocatedBlock_template
#print axioms gasSteps_template
#print axioms template_exactBytes

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedNormalizedStartup
