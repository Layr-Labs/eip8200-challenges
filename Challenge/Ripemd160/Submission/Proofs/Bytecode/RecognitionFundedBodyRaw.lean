import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionControlSimplify

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionFundedBodyRaw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionRecurrence RecognitionBodyRaw
private theorem hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl

def normalTemplate : List Instr :=
  [ .op .JUMPDEST,
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op .CALLDATALOAD,
    .op .XOR,
    .op .OR,
    .op (.Swap ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .ADD,
    .op (.Swap ⟨0, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .NOT,
    .op .AND,
    .op (.Dup ⟨7, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .op (.Dup ⟨7, by decide⟩),
    .op .ADD,
    .op .XOR,
    .op (.Swap ⟨2, by decide⟩),
    .op .POP ]

theorem run_normal (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq normalTemplate {s with pc := pc, stack := frame f rho} =
      some {s with
        pc := pcAfter pc normalTemplate
        stack := frame (normalResult s f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega) [normalTemplate, normalResult, frame, c32,
    advance, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hadd_eq, hmul_eq, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

def boundaryTemplate : List Instr :=
  [ .op (.Dup ⟨8, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 40),
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 8),
    .op .SHR,
    .op .MUL,
    .push ⟨1, by decide⟩ (UInt256.ofNat 216),
    .op .SUB,
    .op .SHR,
    .push ⟨1, by decide⟩ (UInt256.ofNat 11),
    .op .MUL,
    .op (.Dup ⟨3, by decide⟩),
    .op (.Dup ⟨8, by decide⟩),
    .op .AND,
    .op .ADD,
    .op (.Dup ⟨2, by decide⟩),
    .op .CALLDATALOAD,
    .op .XOR,
    .op (.Dup ⟨8, by decide⟩),
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .op .XOR,
    .op .OR,
    .op (.Dup ⟨7, by decide⟩),
    .op (.Dup ⟨3, by decide⟩),
    .op .NOT,
    .op .AND,
    .op (.Dup ⟨9, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 43),
    .op .MUL,
    .op (.Dup ⟨4, by decide⟩),
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op .ADD,
    .op .XOR,
    .op (.Swap ⟨2, by decide⟩),
    .op .POP,
    .op (.Swap ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .ADD,
    .op (.Swap ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op (.Dup ⟨2, by decide⟩),
    .op .ADD,
    .op (.Swap ⟨3, by decide⟩),
    .op .POP ]

theorem run_boundary (s : State) (pc : UInt256) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq boundaryTemplate {s with pc := pc, stack := frame f rho} =
      some {s with
        pc := pcAfter pc boundaryTemplate
        stack := frame (boundaryResult s f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega) [boundaryTemplate, boundaryResult, frame, c32,
    advance, correction, PatternedSwar.straddleAdd, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hadd_eq, hmul_eq, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms run_normal
#print axioms run_boundary
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionFundedBodyRaw
