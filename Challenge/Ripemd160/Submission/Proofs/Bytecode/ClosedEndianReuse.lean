import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
import Batteries.Tactic.OpenPrivate

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianReuse

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
  [op .JUMPDEST, endianFactorPush shift, .op (.Dup ⟨1, by decide⟩), dup1,
   push1 (UInt256.ofNat shift), op .SHR, op .XOR, .op (.Dup ⟨1, by decide⟩),
   .push 0 0, op .NOT, op .DIV, op .AND, op .MUL, op .XOR]

theorem run_endian (s : State) (startPC value : UInt256) (shift : Nat)
    (mask : UInt256) (rest : List UInt256) (hstack : rest.length < 1019)
    (hcase : (shift = 8 ∧ mask = mask8) ∨ (shift = 16 ∧ mask = mask16))
    (hrun : s.halt = .Running) :
    runInstrSeq (code shift) {s with pc := startPC, stack := value :: rest} =
      some {s with
        pc := pcAfter startPC (code shift)
        stack := packedStage value shift mask :: rest} := by
  have hcap (m : Nat) (hm : m ≤ 5) : rest.length + m < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hcap4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
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
        runInstrSeq, Stepper.runInstr, pcAfter, hrun, hcap, hcap2, hcap3, hcap4, hcap5,
        hzero, mask8_div, mask16_div, UInt256.succ, Instr.size,
        Instr.size_push, Instr.size_op, Word.literal_eq_ofNat,
        Word.word_toNat_ofNat, Word.ofNat_add_mod, Word.succ_ofNat, List.exchange, List.getElem?_cons_zero, List.getElem?_cons_succ,
        word_add_assoc, word_add_ofNat_assoc, hsemantic]
    -- the constant push is PUSH2 for shift 8 and PUSH3 for shift 16, so the
    -- second instruction is 3 or 4 bytes wide; seed the chain accordingly.
    first
      | rw [add_ofNat_assoc_hAdd startPC 1 3]
      | rw [add_ofNat_assoc_hAdd startPC 1 4]
    repeat first
      | rw [add_ofNat_assoc_hAdd]
      | rw [add_ofNat_assoc_add]
      | rw [add_ofNat_assoc]
    simp only [add_assoc_explicit, add_assoc_explicit_hAdd,
      add_assoc_hAdd_explicit, word_add_assoc]
    simp [Word.ofNat_add_mod, Nat.add_assoc]
    rw [mul_op]
    convert hsemantic using 1
    all_goals
      simp [UInt256.mul, Fin.mul_def, Nat.mul_comm]

theorem advances (shift : Nat) {instruction : Instr} {s t : State}
    (hmem : instruction ∈ code shift) (hrun : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  simp only [code, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact RepeatedByteWord.runInstr_pc_div hrun
    | apply DenseScheduleLift.runInstr_pc_of_advances ?_ hrun
  all_goals first
    | exact Or.inr (Or.inr rfl)
    | exact Or.inl (Or.inl (by constructor))
    -- the leading JUMPDEST: SharedCallTrace.Advances lists it explicitly
    | exact Or.inl (Or.inr (Or.inr rfl))
    | simp only [endianFactorPush]; split <;>
        exact Or.inl (Or.inl (by constructor))

theorem run_located {artifact : ProgramArtifact} {fork : Fork}
    (shift : Nat) (mask : UInt256)
    (site : StackRoundTemplate.GenericRoundSite artifact fork (code shift))
    (s : State) (value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1019)
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
    (hstack : rest.length < 1019)
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianReuse
