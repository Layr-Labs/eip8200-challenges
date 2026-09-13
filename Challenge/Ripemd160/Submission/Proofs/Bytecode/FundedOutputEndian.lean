import Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianTrunc
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianTrunc16
import Batteries.Tactic.OpenPrivate
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FundedOutputEndian.Stage8
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word
open StackRoundTrace DenseScheduleTemplate DenseScheduleTrace

open private word_add_assoc word_add_ofNat_assoc add_ofNat_assoc
  add_ofNat_assoc_hAdd add_ofNat_assoc_add add_assoc_explicit
  add_assoc_explicit_hAdd add_assoc_hAdd_explicit mul_op
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace

open ClosedEndianTrunc
private theorem local_xor_comm (u v : UInt256) : UInt256.xor u v = UInt256.xor v u := by
  cases u with | mk u =>
  cases v with | mk v =>
  simp [UInt256.xor, Fin.xor, Nat.xor_comm]
/-- Stage 8 with a literal, truncated mask. The factor is kept below the XOR operands. -/
def code : List Instr :=
  [dup1, dup1, push1 (UInt256.ofNat 8), op .SHR, op .XOR,
    .push ⟨19, by decide⟩ mask8Low, op .AND,
    ClosedEndianReuse.factorPush 8, op .MUL, op .XOR]

theorem run_endian (s : State) (startPC value : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1018)
    (hv : value.toNat < 2 ^ 160)
    (hrun : s.halt = .Running) :
    runInstrSeq code {s with pc := startPC, stack := value :: rest} =
      some {s with
        pc := pcAfter startPC code
        stack := packedStage value 8 mask8 :: rest} := by
  have hcap (m : Nat) (hm : m ≤ 6) : rest.length + m < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hcap4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have hsemantic :
      UInt256.xor
        (UInt256.mul (endianFactor 8)
          (UInt256.land mask8Low
            (UInt256.xor (UInt256.shiftRight value (UInt256.ofNat 8)) value))) value =
        packedStage value 8 mask8 := by
    rw [land_mask8Low value hv, Word.land_comm mask8]
    simpa only [multipliedStage, endianDelta, endianFactor] using
      DenseEndianMultiply.multipliedStage8_eq_packedStage value
  simp only [endianFactor] at hsemantic
  norm_num at hsemantic
  simp (config := { maxSteps := 1000000 })
    [code, ClosedEndianReuse.factorPush, endianFactorPush, endianFactor,
      op, push1, push2, push3, dup1,
      runInstrSeq, DataStepper.runInstr, pcAfter, hrun, hcap, hcap2, hcap3, hcap4, hcap5, hcap6,
      UInt256.succ, Instr.size, Instr.size_push, Instr.size_op, Word.literal_eq_ofNat,
      Word.word_toNat_ofNat, Word.ofNat_add_mod, Word.succ_ofNat,
      List.exchange, List.getElem?_cons_zero, List.getElem?_cons_succ,
      word_add_assoc, word_add_ofNat_assoc, hsemantic, Word.land_comm, local_xor_comm]
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
    simp [UInt256.mul, Fin.mul_def, Nat.mul_comm, Word.land_comm, local_xor_comm]

theorem advances {instruction : Instr} {s t : State}
    (hmem : instruction ∈ code) (hrun : DataStepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  simp only [code, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply DenseScheduleLift.runInstr_pc_of_advances ?_ hrun
  all_goals first
    | exact Or.inl (Or.inr (Or.inr rfl))
    | exact Or.inr (Or.inr rfl)
    | exact Or.inl (Or.inl (by constructor))

theorem run_located {artifact : DataProgramArtifact} {fork : Fork}
    (site : StackRoundTemplate.GenericRoundSite artifact fork code)
    (s : State) (value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1018)
    (hv : value.toNat < 2 ^ 160)
    (hrun : s.halt = .Running) :
    DataStepper.runLocatedBlock site.path {s with pc := site.startPC, stack := value :: rest} =
      some {s with pc := site.endPC, stack := packedStage value 8 mask8 :: rest} := by
  have hend : site.endPC = pcAfter site.startPC code := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  have hraw : DataStepper.runLocatedBlock site.path
      {s with pc := site.startPC, stack := value :: rest} =
      runInstrSeq code {s with pc := site.startPC, stack := value :: rest} := by
    apply runLocatedBlock_eq_runInstrSeq_site site _ rfl
    intro located hmem u v hresult
    apply advances ?_ hresult
    rw [← site.instruction_eq]
    exact List.mem_map_of_mem hmem
  rw [hraw, run_endian s site.startPC value rest hstack hv hrun, ← hend]

def gasSteps_endian {artifact : DataProgramArtifact} {fork : Fork}
    (site : StackRoundTemplate.GenericRoundSite artifact fork code)
    (s : State) (value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1018)
    (hv : value.toNat < 2 ^ 160)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.startPC, stack := value :: rest}
      {s with pc := site.endPC, stack := packedStage value 8 mask8 :: rest} := by
  apply DataStepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact run_located site s value rest hstack hv hrun
  · exact hrun
  · exact hnp

#print axioms land_mask8Low
#print axioms packedHash_lt
#print axioms run_endian
#print axioms advances
#print axioms run_located
#print axioms gasSteps_endian

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FundedOutputEndian.Stage8

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FundedOutputEndian.Stage16
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word
open StackRoundTrace DenseScheduleTemplate DenseScheduleTrace

open private word_add_assoc word_add_ofNat_assoc add_ofNat_assoc
  add_ofNat_assoc_hAdd add_ofNat_assoc_add add_assoc_explicit
  add_assoc_explicit_hAdd add_assoc_hAdd_explicit mul_op
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace

open ClosedEndianTrunc16
private theorem local_xor_comm (u v : UInt256) : UInt256.xor u v = UInt256.xor v u := by
  cases u with | mk u =>
  cases v with | mk v =>
  simp [UInt256.xor, Fin.xor, Nat.xor_comm]
/-- Stage 16 with a literal, truncated mask. The factor is kept below the XOR operands. -/
def code : List Instr :=
  [dup1, push1 (UInt256.ofNat 16), op .SHR, .op (.Dup ⟨1, by decide⟩), op .XOR,
    .push ⟨18, by decide⟩ mask16Low, op .AND, ClosedEndianReuse.factorPush 16,
    op .MUL, op .XOR]

theorem run_endian (s : State) (startPC value : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hv : value.toNat < 2 ^ 160)
    (hrun : s.halt = .Running) :
    runInstrSeq code {s with pc := startPC, stack := value :: rest} =
      some {s with
        pc := pcAfter startPC code
        stack := packedStage value 16 mask16 :: rest} := by
  have hcap (m : Nat) (hm : m ≤ 5) : rest.length + m < 1024 := by omega
  have hcap2 : rest.length + 1 + 1 < 1024 := by omega
  have hcap3 : rest.length + 1 + 1 + 1 < 1024 := by omega
  have hcap4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hsemantic :
      UInt256.xor
        (UInt256.mul (endianFactor 16)
          (UInt256.land mask16Low
            (UInt256.xor (UInt256.shiftRight value (UInt256.ofNat 16)) value))) value =
        packedStage value 16 mask16 := by
    rw [land_mask16Low value hv, Word.land_comm mask16]
    simpa only [multipliedStage, endianDelta, endianFactor] using
      DenseEndianMultiply.multipliedStage16_eq_packedStage value
  simp only [endianFactor] at hsemantic
  norm_num at hsemantic
  simp (config := { maxSteps := 1000000 })
    [code, ClosedEndianReuse.factorPush, endianFactorPush, endianFactor,
      op, push1, push2, push3, dup1,
      runInstrSeq, DataStepper.runInstr, pcAfter, hrun, hcap, hcap2, hcap3, hcap4, hcap5,
      UInt256.succ, Instr.size, Instr.size_push, Instr.size_op, Word.literal_eq_ofNat,
      Word.word_toNat_ofNat, Word.ofNat_add_mod, Word.succ_ofNat,
      List.exchange, List.getElem?_cons_zero, List.getElem?_cons_succ,
      word_add_assoc, word_add_ofNat_assoc, hsemantic, Word.land_comm, local_xor_comm]
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
    simp [UInt256.mul, Fin.mul_def, Nat.mul_comm, Word.land_comm, local_xor_comm]

theorem advances {instruction : Instr} {s t : State}
    (hmem : instruction ∈ code) (hrun : DataStepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  simp only [code, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply DenseScheduleLift.runInstr_pc_of_advances ?_ hrun
  all_goals first
    | exact Or.inl (Or.inr (Or.inr rfl))
    | exact Or.inr (Or.inr rfl)
    | exact Or.inl (Or.inl (by constructor))

theorem run_located {artifact : DataProgramArtifact} {fork : Fork}
    (site : StackRoundTemplate.GenericRoundSite artifact fork code)
    (s : State) (value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1019)
    (hv : value.toNat < 2 ^ 160)
    (hrun : s.halt = .Running) :
    DataStepper.runLocatedBlock site.path {s with pc := site.startPC, stack := value :: rest} =
      some {s with pc := site.endPC, stack := packedStage value 16 mask16 :: rest} := by
  have hend : site.endPC = pcAfter site.startPC code := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  have hraw : DataStepper.runLocatedBlock site.path
      {s with pc := site.startPC, stack := value :: rest} =
      runInstrSeq code {s with pc := site.startPC, stack := value :: rest} := by
    apply runLocatedBlock_eq_runInstrSeq_site site _ rfl
    intro located hmem u v hresult
    apply advances ?_ hresult
    rw [← site.instruction_eq]
    exact List.mem_map_of_mem hmem
  rw [hraw, run_endian s site.startPC value rest hstack hv hrun, ← hend]

def gasSteps_endian {artifact : DataProgramArtifact} {fork : Fork}
    (site : StackRoundTemplate.GenericRoundSite artifact fork code)
    (s : State) (value : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1019)
    (hv : value.toNat < 2 ^ 160)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.startPC, stack := value :: rest}
      {s with pc := site.endPC, stack := packedStage value 16 mask16 :: rest} := by
  apply DataStepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact run_located site s value rest hstack hv hrun
  · exact hrun
  · exact hnp

#print axioms land_mask16Low
#print axioms packedHash_lt
#print axioms run_endian
#print axioms advances
#print axioms run_located
#print axioms gasSteps_endian

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FundedOutputEndian.Stage16

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FundedOutputEndian
abbrev code8 := Stage8.code
abbrev code16 := Stage16.code
abbrev gasSteps8 := @Stage8.gasSteps_endian
abbrev gasSteps16 := @Stage16.gasSteps_endian
end Challenge.Ripemd160.Submission.Proofs.Bytecode.FundedOutputEndian
