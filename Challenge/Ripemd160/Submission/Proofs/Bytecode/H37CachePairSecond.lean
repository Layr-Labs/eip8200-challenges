import Challenge.Ripemd160.Submission.Proofs.Bytecode.H37CachePairTemplate

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.H37CachePair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace PairRoundTemplate PairRoundState
open QuadGapTemplate QuadGapTrace

/-- Arbitrary input State and opaque old result; only PC is changed. -/
theorem second_relation (j : Nat) (hj : j < 5) (constant : UInt256)
    (s : State) (oldPC newPC p0 p1 ret : UInt256)
    (r0 r1 : Nat) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1005) (hrun : s.halt = .Running) :
    runInstrSeq (secondTemplate j)
        (pairHelperEntry s newPC p0 p1 ret r0 r1 working (cache constant rho)) =
      (runInstrSeq (pairBeforeJumpTemplate j constant)
          (pairHelperEntry s oldPC p0 p1 ret r0 r1 working (cache constant rho))).map
        (fun out => {out with pc := pcAfter newPC (secondTemplate j)}) := by
  have hcap (n : Nat) (hn : n ≤ 19) : rho.length + n < 1024 := by omega
  have hadd (u v : UInt256) : u + v = u.add v := by rfl
  interval_cases j <;>
    simp (config := {maxSteps := 3000000})
      [firstTemplate, secondTemplate, firstBoolean, secondBoolean, d, w, cache, insertState,
        pairBeforeJumpTemplate, pairFirstBooleanOps, pairSecondBooleanOps,
        pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5, pairSwap7,
        qrot, cfold, op, push1, push4, dup1, dup2, dup3, dup4, dup5, dup6,
        swap1, swap2, swap3, swap4, pairHelperEntry, roundWords,
        runInstrSeq, Stepper.runInstr, List.exchange, List.drop,
        hrun, hcap, factor, pcAfter, UInt256.succ, Instr.size,
        Instr.size_push, Instr.size_op, Nat.add_assoc,
        State.activeWordsAfterUInt256, hadd]

theorem run_second (j : Nat) (hj : j < 5) (constant : UInt256)
    (s : State) (newPC p0 p1 ret : UInt256)
    (r0 r1 : Nat) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1005) (hrun : s.halt = .Running)
    (hzero : j = 0 → constant = 0) (hr0 : r0 ≤ 32) (hr1 : r1 ≤ 32) :
    runInstrSeq (secondTemplate j)
        (pairHelperEntry s newPC p0 p1 ret r0 r1 working (cache constant rho)) =
      some (pairAfterHelperBeforeJump s (pcAfter newPC (secondTemplate j))
        ret j working p0 p1 r0 r1 constant (cache constant rho)) := by
  rw [second_relation j hj constant s 0 newPC p0 p1 ret r0 r1 working rho hstack hrun]
  rw [PairRawTrace.runInstrSeq_template j hj s 0 p0 p1 ret r0 r1 working
    constant (cache constant rho) hzero (by simp only [cache, List.length_cons]; omega)
    hrun hr0 hr1]
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.H37CachePair

