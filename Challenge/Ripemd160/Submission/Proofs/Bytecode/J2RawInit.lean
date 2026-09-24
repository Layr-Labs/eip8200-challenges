import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2RawBase
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionRecurrence
private theorem hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem hsub_eq (a b : UInt256) : a - b = UInt256.sub a b := rfl
private theorem hdiv_eq (a b : UInt256) : a / b = UInt256.div a b := rfl
private theorem hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl
theorem run_init (s : State) (pc : UInt256) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq initTemplate {s with pc := pc, stack := rho} =
      some {s with pc := pcAfter pc initTemplate, stack := frame (initResult s.executionEnv.calldata.size) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  have hU : UInt256.div (UInt256.lnot (UInt256.ofNat 0)) (UInt256.ofNat 255) = PatternedSwar.M := by decide
  have hH : UInt256.shiftLeft PatternedSwar.M (UInt256.ofNat 7) = PatternedSwar.m8 := by decide
  have hL : UInt256.lnot PatternedSwar.m8 = PatternedSwar.m7 := by decide
  have hC : UInt256.ofNat 96 * PatternedSwar.M = c96 := rfl
  have hC2 : UInt256.mul (UInt256.ofNat 96) PatternedSwar.M = c96 := rfl
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [initTemplate, initResult_eq, frame, runInstrSeq, DataStepper.runInstr, pcAfter,
    clamp, aligned, c114, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, hrun, hbase, hcap, hU, hH, hL, hC, hC2,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hsub_eq, hdiv_eq, hU, hH, hL, hC, hC2, hadd_eq, hmul_eq, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms run_init
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
