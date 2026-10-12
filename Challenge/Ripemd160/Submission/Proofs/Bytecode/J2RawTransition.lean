import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2RawBase
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionRecurrence
private theorem hadd_eq (a b : UInt256) : a + b = UInt256.add a b := rfl
private theorem hmul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl
private theorem hsub_eq (a b : UInt256) : a - b = UInt256.sub a b := rfl

theorem repunit_div : UInt256.div c96 (UInt256.ofNat 96) = PatternedSwar.M := by decide

theorem repunit_hdiv : c96 / UInt256.ofNat 96 = PatternedSwar.M := by decide


/-- Reusing the shifted boundary sentinel gives the subtraction constant exactly. -/
theorem complement_sentinel_div9 :
    UInt256.div (UInt256.lnot (UInt256.shiftLeft c96 (UInt256.ofNat 2)))
      (UInt256.ofNat 9) = UInt256.mul (UInt256.ofNat 14) PatternedSwar.M := by decide

/-- The negative sentinel quotient is the additive inverse of the old subtraction constant. -/
theorem signed_sentinel_div9 :
    UInt256.sdiv (UInt256.shiftLeft c96 (UInt256.ofNat 2)) (UInt256.ofNat 9) =
      UInt256.sub (UInt256.ofNat 0) (UInt256.mul (UInt256.ofNat 14) PatternedSwar.M) := by decide

theorem add_negative_eq_sub (a b : UInt256) :
    UInt256.add a (UInt256.sub (UInt256.ofNat 0) b) = UInt256.sub a b := by
  unfold UInt256.add UInt256.sub
  congr 1
  simp [sub_eq_add_neg, UInt256.ofNat]

theorem run_transition (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    runInstrSeq transitionTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc transitionTemplate, stack := f.off :: frame (transitionResult f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [transitionTemplate, transitionResult, frame, c114,
      tw, emin, clamp, aligned, advance, runInstrSeq, DataStepper.runInstr,
      pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
      Nat.add_assoc, hrun, hbase, hcap, signed_sentinel_div9, add_negative_eq_sub, ← hlen,
      Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [signed_sentinel_div9, add_negative_eq_sub, hsub_eq, hadd_eq, hmul_eq,
    RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm,
    RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm,
    RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm,
    RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm,
    RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

#print axioms signed_sentinel_div9
#print axioms complement_sentinel_div9
#print axioms run_transition
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
