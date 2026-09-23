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

def transitionATemplate : List Instr := transitionTemplate.take 14
def transitionBTemplate : List Instr := transitionTemplate.drop 14
def transitionAResult (f : Frame) : Frame := {f with word := advance 114 f.word}
def transitionBResult (f : Frame) : Frame :=
  {f with off := f.stop, stop := emin f.stop f.len,
          full := UInt256.sub (emin f.stop f.len) (UInt256.ofNat 32)}

theorem transitionBResult_eq (f : Frame) : transitionBResult f =
    {f with off := f.stop, stop := emin f.stop f.len,
            full := UInt256.sub (emin f.stop f.len) (UInt256.ofNat 32)} := rfl

theorem run_transitionA_aux (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq (transitionTemplate.take 14) {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc (transitionTemplate.take 14), stack := frame ({f with word := advance 114 f.word} : Frame) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega) [transitionTemplate, frame, c32, c114,
    clamp, aligned, advance, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hsub_eq, hadd_eq, hmul_eq, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

theorem run_transitionB_aux (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    runInstrSeq (transitionTemplate.drop 14) {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc (transitionTemplate.drop 14), stack := frame ({f with off := f.stop, stop := emin f.stop f.len, full := UInt256.sub (emin f.stop f.len) (UInt256.ofNat 32)} : Frame) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega) [transitionTemplate, frame, c32, c114,
    emin, clamp, aligned, advance, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap, ← hlen,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hsub_eq, hadd_eq, hmul_eq, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

theorem run_transitionA (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq transitionATemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc transitionATemplate, stack := frame (transitionAResult f) rho} := by
  simp only [transitionATemplate, transitionAResult]
  exact run_transitionA_aux s pc f rho hstack hrun

theorem run_transitionB (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    runInstrSeq transitionBTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc transitionBTemplate, stack := frame (transitionBResult f) rho} := by
  simp only [transitionBTemplate, transitionBResult]
  exact run_transitionB_aux s pc f rho hstack hrun hlen

theorem run_transition_aux (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    runInstrSeq transitionTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc transitionTemplate, stack := frame ({f with word := advance 114 f.word, off := f.stop, stop := emin f.stop f.len, full := UInt256.sub (emin f.stop f.len) (UInt256.ofNat 32)} : Frame) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega) [transitionTemplate, frame, c32, c114,
    emin, clamp, aligned, advance, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap, ← hlen,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hsub_eq, hadd_eq, hmul_eq, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

theorem run_transition (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    runInstrSeq transitionTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc transitionTemplate, stack := frame (transitionResult f) rho} := by
  simp only [transitionResult]
  exact run_transition_aux s pc f rho hstack hrun hlen

#print axioms run_transitionA
#print axioms run_transitionB
#print axioms run_transition
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
