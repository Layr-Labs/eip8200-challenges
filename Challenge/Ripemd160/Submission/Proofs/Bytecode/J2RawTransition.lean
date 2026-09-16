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

def transitionATemplate : List Instr := transitionTemplate.take 15
def transitionBTemplate : List Instr := transitionTemplate.drop 15
def transitionAResult (f : Frame) : Frame := {f with word := advance 114 f.word, off := f.stop}
def transitionBResult (f : Frame) : Frame :=
  let e := UInt256.add f.off (clamp (UInt256.sub f.len f.off))
  {f with stop := e, full := UInt256.add f.off (aligned (UInt256.sub e f.off))}

/-- The operand of `aligned` here is `e - off`, and `e = off + clamp (len - off)`,
so the operand is exactly `clamp (len - off)` and is therefore below 256. -/
theorem transitionB_operand_lt (f : Frame) :
    (UInt256.sub (UInt256.add f.off (clamp (UInt256.sub f.len f.off))) f.off).toNat
      < 256 := by
  rw [sub_add_self]
  exact clamp_lt _

/-- `transitionBResult` with the `0xE0` mask in place of `~0x1F`.  The operand
`e - off` is deliberately left unreduced, because that is the form the
template's symbolic execution produces. -/
theorem transitionBResult_eq (f : Frame) : transitionBResult f =
    {f with stop := UInt256.add f.off (clamp (UInt256.sub f.len f.off)),
            full := UInt256.add f.off (UInt256.land
              (UInt256.sub (UInt256.add f.off (clamp (UInt256.sub f.len f.off))) f.off)
              (UInt256.ofNat 252))} := by
  unfold transitionBResult
  rw [land224_eq_aligned _ (transitionB_operand_lt f)]

theorem run_transitionA (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running) :
    runInstrSeq transitionATemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc transitionATemplate, stack := frame (transitionAResult f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega) [transitionATemplate, transitionTemplate, transitionAResult, frame, c32, c114,
    clamp, aligned, advance, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hsub_eq, hadd_eq, hmul_eq, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

theorem run_transitionB (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size)
    (hoff : f.off = f.stop) :
    runInstrSeq transitionBTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc transitionBTemplate, stack := frame (transitionBResult f) rho} := by
  have hbase : rho.length < 1024 := by omega
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (config := { maxSteps := 600000 }) (discharger := omega) [transitionBTemplate, transitionTemplate, transitionBResult_eq, frame, c32, c114,
    clamp, aligned, advance, runInstrSeq, DataStepper.runInstr, pcAfter, UInt256.succ, Instr.size,
    List.exchange, List.getElem?_cons_zero, Nat.add_assoc, hrun, hbase, hcap, ← hlen, hoff,
    Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  all_goals simp only [hsub_eq, hadd_eq, hmul_eq, RawExpressionAC.add_assoc, RawExpressionAC.add_comm, RawExpressionAC.add_left_comm, RawExpressionAC.mul_assoc, RawExpressionAC.mul_comm, RawExpressionAC.mul_left_comm, RawExpressionAC.land_assoc, RawExpressionAC.land_comm, RawExpressionAC.land_left_comm, RawExpressionAC.lor_assoc, RawExpressionAC.lor_comm, RawExpressionAC.lor_left_comm, RawExpressionAC.xor_assoc, RawExpressionAC.xor_comm, RawExpressionAC.xor_left_comm]
  all_goals repeat first | apply And.intro | exact True.intro | rfl

theorem run_transition (s : State) (pc : UInt256) (f : Frame) (rho : List UInt256)
    (hstack : rho.length ≤ 990) (hrun : s.halt = .Running)
    (hlen : f.len = UInt256.ofNat s.executionEnv.calldata.size) :
    runInstrSeq transitionTemplate {s with pc := pc, stack := frame f rho} =
      some {s with pc := pcAfter pc transitionTemplate, stack := frame (transitionResult f) rho} := by
  have ha := run_transitionA s pc f rho hstack hrun
  have hb := run_transitionB s (pcAfter pc transitionATemplate) (transitionAResult f) rho hstack hrun (by simpa only [transitionAResult] using hlen) (by simp only [transitionAResult])
  have hab := DenseScheduleTrace.runInstrSeq_append_running ha (by exact hrun) hb
  have ht : transitionATemplate ++ transitionBTemplate = transitionTemplate := List.take_append_drop 15 _
  have hr : transitionBResult (transitionAResult f) = transitionResult f := rfl
  rw [← DenseScheduleTrace.pcAfter_append, ht, hr] at hab
  exact hab

#print axioms run_transitionA
#print axioms run_transitionB
#print axioms run_transition
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Raw
