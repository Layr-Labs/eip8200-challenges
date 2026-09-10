import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompactGuardConstants
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairMultiplyLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputData

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PatternedSwar StackRoundTemplate StackRoundTrace

def code (byte : UInt256) : List Instr :=
  [.push 1 255, .push 0 0, .op .NOT, .op .DIV, .push 1 byte, .op .MUL]

theorem ascii_a : UInt256.ofNat 97 * M = KnownInputData.fullWord := by decide

set_option linter.unusedSimpArgs false in
theorem run_word (byte : UInt256) (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length < 1021) (hrun : s.halt = .Running) :
    runInstrSeq (code byte) {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc (code byte), stack := (byte * M) :: rho} := by
  have h0 : rho.length < 1024 := by omega
  have h1 : rho.length + 1 < 1024 := by omega
  have h2 : rho.length + 2 < 1024 := by omega
  have hzero : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  simp [code, runInstrSeq, Stepper.runInstr, hrun, h0, h1, h2, hzero,
    pcAfter, Instr.size, Instr.size_op, Instr.size_push, UInt256.succ,
    Word.literal_eq_ofNat, CompactGuardConstants.repeated_one_ofNat, hadd]

theorem runInstr_pc_div {s t : State}
    (hresult : Stepper.runInstr (.op .DIV) s = some t) :
    t.pc = s.pc + UInt256.ofNat (Instr.op .DIV).size := by
  by_cases hcap : s.stack.length < 1024
  · rw [Stepper.runInstr, if_pos hcap] at hresult
    cases hs : s.stack with
    | nil => simp [hs] at hresult
    | cons a tail =>
        cases ht : tail with
        | nil => simp [hs, ht] at hresult
        | cons b rest =>
            simp [hs, ht] at hresult
            subst t
            rfl
  · simp [Stepper.runInstr, hcap] at hresult

theorem advances (byte : UInt256) {instruction : Instr} {s t : State}
    (hmem : instruction ∈ code byte) (hresult : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  simp only [code, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact runInstr_pc_div hresult
    | apply PairMultiplyLift.runInstr_pc_of_advances ?_ hresult
  all_goals first
    | exact Or.inr rfl
    | exact Or.inl (Or.inl (by constructor))

theorem run_located {artifact : ProgramArtifact} {fork : Fork}
    (byte : UInt256) (site : GenericRoundSite artifact fork (code byte))
    (s : State) (rho : List UInt256) (hstack : rho.length < 1021)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := rho} =
      some {s with pc := site.endPC, stack := (byte * M) :: rho} := by
  have hend : site.endPC = pcAfter site.startPC (code byte) := by
    have h := endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
      site.head_eq site.end_eq site.contiguous
    rwa [site.instruction_eq] at h
  have hraw : Stepper.runLocatedBlock site.path {s with pc := site.startPC, stack := rho} =
      runInstrSeq (code byte) {s with pc := site.startPC, stack := rho} := by
    apply runLocatedBlock_eq_runInstrSeq_site site _ rfl
    intro located hmem u v hresult
    apply advances byte ?_ hresult
    rw [← site.instruction_eq]
    exact List.mem_map_of_mem hmem
  rw [hraw, run_word byte s site.startPC rho hstack hrun, ← hend]

def gasSteps_word {artifact : ProgramArtifact} {fork : Fork}
    (byte : UInt256) (site : GenericRoundSite artifact fork (code byte))
    (s : State) (rho : List UInt256) (hstack : rho.length < 1021)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := site.startPC, stack := rho}
      {s with pc := site.endPC, stack := (byte * M) :: rho} := by
  apply Stepper.runLocatedBlock_sound artifact fork site.path
  · exact hcode
  · exact hfork
  · exact run_located byte site s rho hstack hrun
  · exact hrun
  · exact hnp

#print axioms run_word
#print axioms gasSteps_word

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
