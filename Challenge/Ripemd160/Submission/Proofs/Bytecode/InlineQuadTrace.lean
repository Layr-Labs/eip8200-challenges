import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-! Append-only specialization, derived from public PR342 and the Astra scout.
The return token is retained through the existing quad evaluator, then popped.
No helper entry JUMPDEST or terminal JUMP is executed in the inline body. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.InlineQuadTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate

abbrev args (ret p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat) : List Instr :=
  (QuadCallTrace.quadCallPushes ret p0 p1 p2 p3 0 r0 r1 r2 r3).take 9

def body (j : Nat) (constant : UInt256) : List Instr :=
  (quadBeforeJumpTemplate j constant).drop 1

def template (j : Nat) (constant ret p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) : List Instr :=
  args ret p0 p1 p2 p3 r0 r1 r2 r3 ++ body j constant ++ [op .POP]

theorem head_body (j : Nat) (constant : UInt256) :
    quadBeforeJumpTemplate j constant = op .JUMPDEST :: body j constant := by
  rfl

def result (s : State) (pc : UInt256) (j : Nat)
    (working : Compression.EvmWorking) (p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (constant : UInt256) (rho : List UInt256) : State :=
  roundEntry
    {s with activeWords := quadActiveWordsAfterUInt256_4 s
      p0.toNat p1.toNat p2.toNat p3.toNat}
    pc (quadWorking s working j p0 p1 p2 p3 r0 r1 r2 r3 constant).a
    (quadWorking s working j p0 p1 p2 p3 r0 r1 r2 r3 constant).b
    (quadWorking s working j p0 p1 p2 p3 r0 r1 r2 r3 constant).c
    (quadWorking s working j p0 p1 p2 p3 r0 r1 r2 r3 constant).d
    (quadWorking s working j p0 p1 p2 p3 r0 r1 r2 r3 constant).e
    (QuadRoundTemplate.factor :: rho)

theorem run_inline (j : Nat) (hj : j < 5)
    (s : State) (pc ghostPC ret p0 p1 p2 p3 : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (constant : UInt256) (rho : List UInt256)
    (hghost : ghostPC.succ = pcAfter pc (args ret p0 p1 p2 p3 r0 r1 r2 r3))
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32) :
    runInstrSeq (template j constant ret p0 p1 p2 p3 r0 r1 r2 r3)
      (roundEntry s pc working.a working.b working.c working.d working.e
        (QuadRoundTemplate.factor :: rho)) =
      some (result s
        (pcAfter pc (template j constant ret p0 p1 p2 p3 r0 r1 r2 r3))
        j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  let argPC := pcAfter pc (args ret p0 p1 p2 p3 r0 r1 r2 r3)
  let bodyPC := pcAfter argPC (body j constant)
  have hcap (n : Nat) (hn : n ≤ 16) : rho.length + n < 1024 := by omega
  have hp : runInstrSeq (args ret p0 p1 p2 p3 r0 r1 r2 r3)
      (roundEntry s pc working.a working.b working.c working.d working.e
        (QuadRoundTemplate.factor :: rho)) =
      some (quadHelperEntry s argPC p0 p1 p2 p3 ret r0 r1 r2 r3 working rho) := by
    simp (discharger := omega) [args, QuadCallTrace.quadCallPushes, argPC,
      quadHelperEntry, roundEntry, runInstrSeq, Stepper.runInstr, pcAfter,
      push1, push2, hrun, hcap, Nat.add_assoc, Instr.size_push, roundWords]
  have hq := QuadRoundTrace.runInstrSeq_quad j hj s ghostPC p0 p1 p2 p3 ret
    r0 r1 r2 r3 working constant rho hzero hstack hrun hrot0 hrot1 hrot2 hrot3
  rw [head_body] at hq
  have hb : runInstrSeq (body j constant)
      (quadHelperEntry s argPC p0 p1 p2 p3 ret r0 r1 r2 r3 working rho) =
      some (quadAfterHelperBeforeJump s bodyPC ret j working
        p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
    simpa [runInstrSeq, Stepper.runInstr, quadHelperEntry, op, hrun, hcap,
      roundWords, pcAfter, hghost, argPC, bodyPC, Instr.size_op,
      UInt256.succ] using hq
  have hpop : runInstrSeq [op .POP]
      (quadAfterHelperBeforeJump s bodyPC ret j working
        p0 p1 p2 p3 r0 r1 r2 r3 constant rho) =
      some (result s bodyPC.succ j working p0 p1 p2 p3
        r0 r1 r2 r3 constant rho) := by
    simp [runInstrSeq, Stepper.runInstr, op, quadAfterHelperBeforeJump,
      PairRoundState.pairAfterHelperBeforeJump, result, roundEntry, roundWords,
      quadWorking, quadFirstState, quadFirstWorking, quadActiveWordsAfterUInt256_4,
      hrun, hcap]
  have hbp := QuadRoundState.runInstrSeq_append hb (by
    simp [quadAfterHelperBeforeJump, PairRoundState.pairAfterHelperBeforeJump,
      quadFirstState, hrun]) hpop
  have hall := QuadRoundState.runInstrSeq_append hp (by exact hrun) hbp
  simpa [template, QuadRoundState.pcAfter_append, bodyPC, argPC, pcAfter,
    op, Instr.size_op, UInt256.succ, List.append_assoc] using hall

theorem advances (j : Nat) (hj : j < 5)
    (constant ret p0 p1 p2 p3 : UInt256) (r0 r1 r2 r3 : Nat) :
    ∀ i ∈ template j constant ret p0 p1 p2 p3 r0 r1 r2 r3,
      PairMultiplyLift.Advances i := by
  intro i hi
  simp only [template, List.mem_append] at hi
  rcases hi with (ha | hb) | hp
  · exact Or.inl (QuadCallTrace.quadCallPushes_advances ret p0 p1 p2 p3 0
      r0 r1 r2 r3 i (List.mem_of_mem_take ha))
  · exact QuadHelperTrace.template_advances j hj constant i (List.mem_of_mem_drop hb)
  · have heq : i = op .POP := by simpa using hp
    rw [heq]
    exact Or.inl (Or.inl (by constructor))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.InlineQuadTrace
