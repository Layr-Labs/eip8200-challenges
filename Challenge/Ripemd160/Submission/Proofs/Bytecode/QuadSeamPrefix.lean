import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamCancel

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# Quad helper prefix before seam cancellation

This module evaluates the byte-identical helper prefix up to the point where
the legacy and optimized stack sequences differ.  It deliberately reuses the
generic pair evaluator and does not inspect the full submission artifact.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamPrefix

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTemplate StackRoundTrace PairRoundTemplate PairRoundState
open QuadGapTemplate QuadGapTrace QuadSeamCancel

def insertPreSeamState (extra : List UInt256) (pc : UInt256)
    (s : State) : State :=
  {s with
    pc := pc
    stack := (s.stack.drop 1).take 1 ++ extra ++ s.stack.take 1 ++
      s.stack.drop 2}

set_option linter.unusedSimpArgs false in
theorem run_prefix_congruence (j : Nat) (hj : j < 5) (constant : UInt256)
    (s : State) (oldPC newPC p0 p1 ret e0 e1 e2 e3 : UInt256)
    (r0 r1 : Nat) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running) :
    runInstrSeq (seamPrefix j constant)
        (insertState 5 [e0, e1, e2, e3] newPC
          (pairHelperEntry s oldPC p0 p1 ret r0 r1 working (factor :: rho))) =
      (runInstrSeq (pairBeforeJumpTemplate j constant)
          (pairHelperEntry s oldPC p0 p1 ret r0 r1 working (factor :: rho))).map
        (insertPreSeamState [e0, e1, e2, e3]
          (pcAfter newPC (seamPrefix j constant))) := by
  have hcap (n : Nat) (hn : n ≤ 17) : rho.length + n < 1024 := by omega
  have hadd (u v : UInt256) : u + v = u.add v := by rfl
  interval_cases j <;>
    simp (config := {maxSteps := 3000000})
      [seamPrefix, firstFTemplate, firstBoolean, secondBoolean, d, w,
        insertState, insertPreSeamState,
        pairBeforeJumpTemplate, pairFirstBooleanOps, pairSecondBooleanOps,
        pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5, pairSwap7,
        qrot, cfold, op, push1, push4, dup1, dup2, dup3, dup4, dup5, dup6,
        swap1, swap2, swap3, swap4, pairHelperEntry, roundWords,
        runInstrSeq, Stepper.runInstr, List.exchange,
        hrun, hcap, factor, pcAfter, UInt256.succ, Instr.size,
        Instr.size_push, Instr.size_op, Nat.add_assoc,
        State.activeWordsAfterUInt256, hadd]

theorem run_prefix (j : Nat) (hj : j < 5) (constant : UInt256)
    (s : State) (newPC p0 p1 ret e0 e1 e2 e3 : UInt256)
    (r0 r1 : Nat) (working : Compression.EvmWorking) (rho : List UInt256)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hzero : j = 0 → constant = 0) (hr0 : r0 ≤ 32) (hr1 : r1 ≤ 32) :
    runInstrSeq (seamPrefix j constant)
        (insertState 5 [e0, e1, e2, e3] newPC
          (pairHelperEntry s 0 p0 p1 ret r0 r1 working (factor :: rho))) =
      some (insertPreSeamState [e0, e1, e2, e3]
        (pcAfter newPC (seamPrefix j constant))
        (pairAfterHelperBeforeJump s
          (pcAfter 0 (pairBeforeJumpTemplate j constant)) ret j working
          p0 p1 r0 r1 constant (factor :: rho))) := by
  rw [run_prefix_congruence j hj constant s 0 newPC p0 p1 ret e0 e1 e2 e3
    r0 r1 working rho hstack hrun]
  rw [PairRawTrace.runInstrSeq_template j hj s 0 p0 p1 ret r0 r1 working
    constant (factor :: rho) hzero
    (by simp only [List.length_cons]; omega) hrun hr0 hr1]
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamPrefix
