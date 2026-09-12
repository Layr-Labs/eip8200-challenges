import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionBranchRaw

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionControlSimplify
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionRecurrence RecognitionBodyRaw

private theorem hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl

/-- A boundary body entered by fallthrough needs no jump-destination marker. -/
def boundaryTemplate : List Instr := RecognitionBodyRaw.boundaryTemplate.drop 1

theorem boundary_decomposition :
    RecognitionBodyRaw.boundaryTemplate = .op .JUMPDEST :: boundaryTemplate := rfl

theorem run_boundary (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq boundaryTemplate {s with pc := pc, stack := frame f rho} =
      some {s with
        pc := pcAfter pc boundaryTemplate
        stack := frame (boundaryResult s f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [boundaryTemplate, RecognitionBodyRaw.boundaryTemplate, boundaryResult, frame, c32,
      advance, correction, PatternedSwar.straddleAdd, runInstrSeq, Stepper.runInstr,
      pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
      Nat.add_assoc, hrun, hbase, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hadd_eq, hmul_eq,
    RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm,
    RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm,
    RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm,
    RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

/-- Initialization and the backedge share one retained destination marker. -/
def passTemplate : List Instr := [.op .JUMPDEST]

theorem run_pass (s : State) (pc : UInt256) (stack : List UInt256)
    (hstack : stack.length < 1024) (hrun : s.halt = .Running) :
    runInstrSeq passTemplate {s with pc := pc, stack := stack} =
      some {s with pc := pcAfter pc passTemplate, stack := stack} := by
  simp [passTemplate, runInstrSeq, Stepper.runInstr, pcAfter, hstack, hrun]
  rfl

/-- The rejected scanner frame (below the consumed accumulator) is discarded before falling
through to the generic path. -/
def cleanupTemplate : List Instr :=
  [.op .JUMPDEST, .op .POP, .op .POP, .op .POP, .op .POP,
    .op .POP, .op .POP, .op .POP, .op .POP]

theorem run_cleanup (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq cleanupTemplate {s with pc := pc, stack := RecognitionBranchRaw.finishRest f rho} =
      some {s with pc := pcAfter pc cleanupTemplate, stack := rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [cleanupTemplate, RecognitionBranchRaw.finishRest, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals rfl

theorem boundary_length : boundaryTemplate.length = 46 := rfl
theorem boundary_bytes : (boundaryTemplate.map Instr.size).sum = 53 := rfl
theorem pass_length : passTemplate.length = 1 := rfl
theorem pass_bytes : (passTemplate.map Instr.size).sum = 1 := rfl
theorem cleanup_length : cleanupTemplate.length = 9 := rfl
theorem cleanup_bytes : (cleanupTemplate.map Instr.size).sum = 9 := rfl

theorem removed_jumpdest_cost (s : State) :
    Stepper.instrCost (.op .JUMPDEST) s = 1 := rfl

theorem removed_jump_cost (s : State) (dest : Nat) :
    Stepper.instrCost (.push ⟨2, by decide⟩ (UInt256.ofNat dest)) s +
      Stepper.instrCost (.op .JUMP) s = 11 := rfl

#print axioms run_boundary
#print axioms run_pass
#print axioms run_cleanup
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionControlSimplify
