import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamPrefix

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-! Contextual equality between the optimized and legacy four-round helpers. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamCancel
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamPrefix

theorem runInstrSeq_quad_eq_legacy (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (constant : UInt256) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32) :
    runInstrSeq (quadBeforeJumpTemplate j constant)
        (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
          r0 r1 r2 r3 working rho) =
      runInstrSeq (legacyQuadBeforeJumpTemplate j constant)
        (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
          r0 r1 r2 r3 working rho) := by
  let firstWorking : Compression.EvmWorking :=
    quadFirstWorking s working j p0 p1 r0 r1 constant
  let entry : State :=
    quadHelperEntry s startPC p0 p1 p2 p3 returnPC
      r0 r1 r2 r3 working rho
  let seamState : State :=
    insertPreSeamState
      [p2, UInt256.ofNat (32 - r2), p3, UInt256.ofNat (32 - r3)]
      (pcAfter startPC (seamPrefix j constant))
      (pairAfterHelperBeforeJump s
        (pcAfter 0 (pairBeforeJumpTemplate j constant))
        returnPC j working p0 p1 r0 r1 constant
          (QuadGapTemplate.factor :: rho))
  have hprefixRaw := QuadSeamPrefix.run_prefix j hj constant s startPC p0 p1
    returnPC p2 (UInt256.ofNat (32 - r2)) p3 (UInt256.ofNat (32 - r3))
    r0 r1 working rho hstack hrun hzero hrot0 hrot1
  have hprefix :
      runInstrSeq (seamPrefix j constant) entry =
        some {seamState with stack :=
          [firstWorking.a, p2, UInt256.ofNat (32 - r2), p3,
            UInt256.ofNat (32 - r3), returnPC, firstWorking.b,
            firstWorking.c, firstWorking.d, firstWorking.e,
            QuadRoundTemplate.factor] ++ rho} := by
    simpa [entry, seamState, insertPreSeamState, firstWorking,
      quadHelperEntry, insertState, pairHelperEntry,
      pairAfterHelperBeforeJump, roundWords, quadFirstWorking,
      QuadGapTemplate.factor, QuadRoundTemplate.factor] using hprefixRaw
  have hseamRunning : seamState.halt = .Running := by
    simp [seamState, insertPreSeamState, pairAfterHelperBeforeJump, hrun]
  have hcontext := QuadSeamCancel.runInstrSeq_optimized_quad_context
    j hj constant entry seamState
    firstWorking.a p2 (UInt256.ofNat (32 - r2)) p3
    (UInt256.ofNat (32 - r3)) returnPC firstWorking.b firstWorking.c
    firstWorking.d firstWorking.e QuadRoundTemplate.factor rho hstack hprefix
    hseamRunning
  rw [show entry = quadHelperEntry s startPC p0 p1 p2 p3 returnPC
    r0 r1 r2 r3 working rho by rfl] at hcontext
  simpa only [quadBeforeJumpTemplate, legacyQuadBeforeJumpTemplate] using hcontext

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace
