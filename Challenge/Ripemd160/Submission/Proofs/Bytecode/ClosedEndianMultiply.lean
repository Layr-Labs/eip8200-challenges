import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
import Batteries.Tactic.OpenPrivate

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianMultiply

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word
open StackRoundTrace DenseScheduleTemplate DenseScheduleTrace

open private word_add_assoc word_add_ofNat_assoc add_ofNat_assoc
  add_ofNat_assoc_hAdd add_ofNat_assoc_add add_assoc_explicit
  add_assoc_explicit_hAdd add_assoc_hAdd_explicit mul_op
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace

theorem mask8_div :
    UInt256.lnot (UInt256.ofNat 0) / UInt256.ofNat 257 = mask8 := by decide

theorem mask16_div :
    UInt256.lnot (UInt256.ofNat 0) / UInt256.ofNat 65537 = mask16 := by decide

def code (shift : Nat) : List Instr :=
  [dup1, dup1, push1 (UInt256.ofNat shift), op .SHR, op .XOR,
   endianFactorPush shift, .push 0 0, op .NOT, op .DIV, op .AND,
   endianFactorPush shift, op .MUL, op .XOR]
def code16 : List Instr :=
  DenseScheduleTemplate.endianStage 16 mask16 ++
    [op .JUMPDEST, op .JUMPDEST, op .JUMPDEST]

theorem run_endian16 (s : State) (startPC value : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1020)
    (hrun : s.halt = .Running) :
    runInstrSeq (code16) {s with pc := startPC, stack := value :: rest} =
      some {s with
        pc := pcAfter startPC (code16)
        stack := packedStage value 16 mask16 :: rest} := by
  have hstage := DenseScheduleTrace.runInstrSeq_endianStage s startPC value
    16 mask16 rest hstack (Or.inr ⟨rfl, rfl⟩) hrun
  have hcap (m : Nat) (hm : m ≤ 3) : rest.length + m < 1024 := by omega
  have hpad :
      runInstrSeq [op .JUMPDEST, op .JUMPDEST, op .JUMPDEST]
        {s with
          pc := pcAfter startPC (endianStage 16 mask16)
          stack := packedStage value 16 mask16 :: rest} =
      some {s with
        pc := pcAfter (pcAfter startPC (endianStage 16 mask16))
          [op .JUMPDEST, op .JUMPDEST, op .JUMPDEST]
        stack := packedStage value 16 mask16 :: rest} := by
    simp [runInstrSeq, Stepper.runInstr, op, pcAfter, hrun, hcap,
      UInt256.succ, Instr.size, Instr.size_op]
  have hjoined := DenseScheduleTrace.runInstrSeq_append_running hstage
    (by simpa [stageState] using hrun) hpad
  simpa [code16, pcAfter_append, stageState] using hjoined

theorem advances16 {instruction : Instr} {s t : State}
    (hmem : instruction ∈ code16)
    (hrun : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  have hstage : ∀ {instruction : Instr},
      instruction ∈ DenseScheduleTemplate.endianStage 16 mask16 →
        DenseScheduleLift.Advances instruction := by
    intro instruction hmem
    simp only [DenseScheduleTemplate.endianStage, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inr (Or.inr rfl)
      | exact Or.inl (Or.inl (by constructor))
      | simp only [DenseScheduleTemplate.endianMaskPush]; split <;>
          exact Or.inl (Or.inl (by constructor))
      | simp only [DenseScheduleTemplate.endianFactorPush]; split <;>
          exact Or.inl (Or.inl (by constructor))
  apply DenseScheduleLift.runInstr_pc_of_advances ?_ hrun
  simp only [code16, List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact hstage hmem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    all_goals exact Or.inl (Or.inr (Or.inr rfl))


theorem run_endian (s : State) (startPC value : UInt256) (shift : Nat)
    (mask : UInt256) (rest : List UInt256) (hstack : rest.length < 1020)
    (hcase : (shift = 8 ∧ mask = mask8) ∨ (shift = 16 ∧ mask = mask16))
    (hrun : s.halt = .Running) :
    runInstrSeq (code shift) {s with pc := startPC, stack := value :: rest} =
      some {s with
        pc := pcAfter startPC (code shift)
        stack := packedStage value shift mask :: rest} := by
  have hcap (m : Nat) (hm : m ≤ 4) : rest.length + m < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hcap4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hzero : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hsemantic :
      UInt256.xor
        (UInt256.mul (endianFactor shift)
          (UInt256.land mask
            (UInt256.xor (UInt256.shiftRight value (UInt256.ofNat shift)) value))) value =
        packedStage value shift mask := by
    rw [Word.land_comm mask]
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa only [multipliedStage, endianDelta, endianFactor] using
        DenseEndianMultiply.multipliedStage8_eq_packedStage value
    · simpa only [multipliedStage, endianDelta, endianFactor] using
        DenseEndianMultiply.multipliedStage16_eq_packedStage value
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [endianFactor] at hsemantic
  all_goals norm_num at hsemantic
  all_goals
    simp (config := { maxSteps := 1000000 })
      [code, endianFactorPush, endianFactor, op, push1, push2, push3, dup1,
        runInstrSeq, Stepper.runInstr, pcAfter, hrun, hcap, hcap2, hcap3, hcap4,
        hzero, mask8_div, mask16_div, UInt256.succ, Instr.size,
        Instr.size_push, Instr.size_op, Word.literal_eq_ofNat,
        Word.word_toNat_ofNat, Word.ofNat_add_mod, Word.succ_ofNat,
        word_add_assoc, word_add_ofNat_assoc, hsemantic]
    rw [add_ofNat_assoc startPC 1 1]
    repeat first
      | rw [add_ofNat_assoc_hAdd]
      | rw [add_ofNat_assoc_add]
      | rw [add_ofNat_assoc]
    simp only [add_assoc_explicit, add_assoc_explicit_hAdd,
      add_assoc_hAdd_explicit, word_add_assoc]
    simp [Word.ofNat_add_mod, Nat.add_assoc]
    rw [mul_op]
    exact hsemantic

theorem advances (shift : Nat) {instruction : Instr} {s t : State}
    (hmem : instruction ∈ code shift) (hrun : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  simp only [code, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals first
    | exact RepeatedByteWord.runInstr_pc_div hrun
    | apply DenseScheduleLift.runInstr_pc_of_advances ?_ hrun
  all_goals first
    | exact Or.inr (Or.inr rfl)
    | exact Or.inl (Or.inl (by constructor))
    | simp only [endianFactorPush]; split <;>
        exact Or.inl (Or.inl (by constructor))

theorem run_located {artifact : ProgramArtifact} {fork : Fork}
    (shift : Nat) (mask : UInt256)
    (site : StackRoundTemplate.GenericRoundSite artifact fork (code shift))
    (s : State) (value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1020)
    (hcase : (shift = 8 ∧ mask = mask8) ∨ (shift = 16 ∧ mask = mask16))
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := value :: rest} =
      some {s with pc := site.endPC, stack := packedStage value shift mask :: rest} := by
  have hend : site.endPC = pcAfter site.startPC (code shift) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  have hraw : Stepper.runLocatedBlock site.path
      {s with pc := site.startPC, stack := value :: rest} =
      runInstrSeq (code shift) {s with pc := site.startPC, stack := value :: rest} := by
    apply runLocatedBlock_eq_runInstrSeq_site site _ rfl
    intro located hmem u v hresult
    apply advances shift ?_ hresult
    rw [← site.instruction_eq]
    exact List.mem_map_of_mem hmem
  rw [hraw, run_endian s site.startPC value shift mask rest hstack hcase hrun, ← hend]

def gasSteps_endian {artifact : ProgramArtifact} {fork : Fork}
    (shift : Nat) (mask : UInt256)
    (site : StackRoundTemplate.GenericRoundSite artifact fork (code shift))
    (s : State) (value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1020)
    (hcase : (shift = 8 ∧ mask = mask8) ∨ (shift = 16 ∧ mask = mask16))
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.startPC, stack := value :: rest}
      {s with pc := site.endPC, stack := packedStage value shift mask :: rest} := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact run_located shift mask site s value rest hstack hcase hrun
  · exact hrun
  · exact hnp

#print axioms mask8_div
#print axioms mask16_div
#print axioms run_endian
#print axioms advances
#print axioms run_located
#print axioms gasSteps_endian

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianMultiply
