import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired15Raw
set_option warningAsError true
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawPaired15
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StaggerRaw

abbrev template : List Instr :=
  StaggerRawPaired15.template.take 14 ++ StaggerRawPaired15.template.drop 17

private theorem zero_hadd (a : UInt256) : UInt256.add (UInt256.ofNat 0) a = a := by
  apply Word.word_ext
  cases a
  simp [UInt256.add, UInt256.ofNat, UInt256.toNat]

private theorem hadd_zero (a : UInt256) : UInt256.add a (UInt256.ofNat 0) = a := by
  apply Word.word_ext
  cases a
  simp [UInt256.add, UInt256.ofNat, UInt256.toNat]

private theorem neutral_hadd (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem neutral_hmul (a b : UInt256) : a * b = UInt256.mul a b := rfl

theorem run_actual (s : State) (pc : UInt256) (x : Input) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hz : MachineState.readWord s.memory 990 = UInt256.ofNat 0) :
    runInstrSeq template {s with pc := pc, stack := StaggerRawPaired15.inputStack x rho} =
      some {s with pc := pcAfter pc template, stack := StaggerRawPaired15.outputStack s.memory x rho} := by
  have hbase : rho.length < 1024 := by omega
  have hzero : ({val := 0} : UInt256).toNat = 0 := rfl
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [template, StaggerRawPaired15.template, StaggerRawPaired15.inputStack,
    StaggerRawPaired15.outputStack, runInstrSeq, DataStepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hzero, hcap, Word.word_toNat_ofNat,
    Word.literal_eq_ofNat, hz, zero_hadd, hadd_zero,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm,
    RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm,
    RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals simp only [neutral_hadd, neutral_hmul, zero_hadd, hadd_zero,
    RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm,
    RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm,
    RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm,
    RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms run_actual
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadCopy.RawPaired15
