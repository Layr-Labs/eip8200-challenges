import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundEquiv
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundLegacyResult

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-! Active four-round evaluator obtained by contextual seam replacement. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRound
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamCancel
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamPrefix

theorem runInstrSeq_quad (j : Nat) (hj : j < 5)
    (s : State) (startPC p0 p1 p2 p3 returnPC : UInt256)
    (r0 r1 r2 r3 : Nat) (working : Compression.EvmWorking)
    (constant : UInt256) (rho : List UInt256)
    (hzero : j = 0 → constant = 0)
    (hstack : rho.length < 1007) (hrun : s.halt = .Running)
    (hrot0 : r0 ≤ 32) (hrot1 : r1 ≤ 32)
    (hrot2 : r2 ≤ 32) (hrot3 : r3 ≤ 32) :
    runInstrSeq (quadBeforeJumpTemplate j constant)
      (quadHelperEntry s startPC p0 p1 p2 p3 returnPC
        r0 r1 r2 r3 working rho) =
      some (quadAfterHelperBeforeJump s
        (pcAfter startPC (quadBeforeJumpTemplate j constant))
        returnPC j working p0 p1 p2 p3 r0 r1 r2 r3 constant rho) := by
  have heq := runInstrSeq_quad_eq_legacy j hj s startPC p0 p1 p2 p3
    returnPC r0 r1 r2 r3 working constant rho hzero hstack hrun hrot0 hrot1
  have hlegacy := runInstrSeq_legacy_quad_optimized_pc j hj s startPC p0 p1 p2 p3
    returnPC r0 r1 r2 r3 working constant rho hzero hstack hrun
    hrot0 hrot1 hrot2 hrot3
  exact heq.trans hlegacy

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTrace
