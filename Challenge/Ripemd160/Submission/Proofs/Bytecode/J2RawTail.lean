import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2RawBase
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionRecurrence
private theorem hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem hsub_eq (a b : UInt256) : a - b = UInt256.sub a b := rfl
private theorem hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl
theorem run_tail (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq tailTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc tailTemplate, stack := pending s f rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [tailTemplate, pending, tailDiff, frame, runInstrSeq, DataStepper.runInstr,
      pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
      Nat.add_assoc, hrun, hbase, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hadd_eq, hmul_eq, hsub_eq, RawExpressionAC.xor_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

theorem run_finalProjection (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hfinal : f.len.toNat ≤ f.stop.toNat)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
    (hactive : s.activeWords = UInt256.ofNat 1) :
    runInstrSeq finalProjectionTemplate {s with pc := pc, stack := pending s f rho} =
      some {s with pc := pcAfter pc finalProjectionTemplate, stack := frame (tailResult s f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [finalProjectionTemplate, pending, tailDiff, tailResult, frame, Nat.not_lt_of_ge hfinal, runInstrSeq, DataStepper.runInstr,
      pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
      Nat.add_assoc, hrun, hbase, hcap, ← hlen, MachineState.msize, hactive,
      Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hadd_eq, hmul_eq, hsub_eq, RawExpressionAC.xor_comm, RawExpressionAC.add_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

theorem run_boundaryProjection (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hboundary : f.stop.toNat < f.len.toNat) :
    runInstrSeq boundaryProjectionTemplate {s with pc := pc, stack := pending s f rho} =
      some {s with pc := pcAfter pc boundaryProjectionTemplate, stack := frame (tailResult s f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [boundaryProjectionTemplate, pending, tailDiff, tailResult, frame, hboundary,
      runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
      List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
      Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hadd_eq, hmul_eq, hsub_eq, RawExpressionAC.xor_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms run_tail
#print axioms run_finalProjection
#print axioms run_boundaryProjection
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
