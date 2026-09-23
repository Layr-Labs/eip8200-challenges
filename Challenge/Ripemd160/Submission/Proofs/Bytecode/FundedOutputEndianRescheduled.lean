import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FundedOutputEndian
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.FundedOutputEndianRescheduled
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
/-- Stage 16 with the resident full-width mask read from the stack. The factor is kept below the XOR operands. -/
def code : List Instr :=
  [dup1, dup1, push1 (UInt256.ofNat 16), op .SHR, op .XOR,
    .op (.Dup ⟨5, by decide⟩), op .AND,
    ClosedEndianReuse.factorPush 16, op .MUL, op .XOR]

theorem run_endian (s : State) (startPC value : UInt256)
    (a b c : UInt256) (rest : List UInt256) (hstack : rest.length < 1010)
    (hrun : s.halt = .Running) :
    runInstrSeq code {s with pc := startPC, stack := value :: a :: b :: c :: mask16 :: rest} =
      some {s with
        pc := pcAfter startPC code
        stack := packedStage value 16 mask16 :: a :: b :: c :: mask16 :: rest} := by
  have hcap (n : Nat) (hn : n ≤ 14) : rest.length + n < 1024 := by omega
  rw [← DenseEndianMultiply.multipliedStage16_eq_packedStage]
  simp (discharger := omega) [code, ClosedEndianReuse.factorPush, endianFactor, multipliedStage, endianDelta,
    op, push1, dup1, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size, hrun, hcap,
    Nat.add_assoc, List.getElem?_cons_zero, List.exchange, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  refine ⟨rfl, ?_⟩
  first
    | rfl
    | (rw [RawExpressionAC.land_comm]; rfl)

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
    (s : State) (value : UInt256) (a b c : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1010)
    (hrun : s.halt = .Running) :
    DataStepper.runLocatedBlock site.path {s with pc := site.startPC, stack := value :: a :: b :: c :: mask16 :: rest} =
      some {s with pc := site.endPC, stack := packedStage value 16 mask16 :: a :: b :: c :: mask16 :: rest} := by
  have hend : site.endPC = pcAfter site.startPC code := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  have hraw : DataStepper.runLocatedBlock site.path
      {s with pc := site.startPC, stack := value :: a :: b :: c :: mask16 :: rest} =
      runInstrSeq code {s with pc := site.startPC, stack := value :: a :: b :: c :: mask16 :: rest} := by
    apply runLocatedBlock_eq_runInstrSeq_site site _ rfl
    intro located hmem u v hresult
    apply advances ?_ hresult
    rw [← site.instruction_eq]
    exact List.mem_map_of_mem hmem
  rw [hraw, run_endian s site.startPC value a b c rest hstack hrun, ← hend]

def gasSteps_endian {artifact : DataProgramArtifact} {fork : Fork}
    (site : StackRoundTemplate.GenericRoundSite artifact fork code)
    (s : State) (value : UInt256) (a b c : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1010)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.startPC, stack := value :: a :: b :: c :: mask16 :: rest}
      {s with pc := site.endPC, stack := packedStage value 16 mask16 :: a :: b :: c :: mask16 :: rest} := by
  apply DataStepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact run_located site s value a b c rest hstack hrun
  · exact hrun
  · exact hnp

#print axioms run_endian
#print axioms advances
#print axioms run_located
#print axioms gasSteps_endian

end Challenge.Ripemd160.Submission.Proofs.Bytecode.FundedOutputEndianRescheduled
