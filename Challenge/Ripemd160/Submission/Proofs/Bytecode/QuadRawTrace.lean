import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRawTrace0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRawTrace1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRawTrace2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRawTrace3
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRawTrace4

set_option warningAsError true
set_option maxRecDepth 30000

/-! Q4M raw dispatch: select the evaluator theorem for the helper group. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRawTrace

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Compression
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState

theorem runInstrSeq_template (j : Nat) (hj : j < 5) (s : State) (startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 constant : UInt256)
    (x : EvmWorking) (rest : List UInt256)
    (hstack : rest.length < 1000) (hrun : s.halt = .Running)
    (hactive : 67 ≤ s.activeWords.toNat)
    (hp0 : p0.toNat + 32 ≤ 2144) (hp1 : p1.toNat + 32 ≤ 2144)
    (hp2 : p2.toNat + 32 ≤ 2144) (hp3 : p3.toNat + 32 ≤ 2144) :
    runInstrSeq (quadBeforeJumpTemplate j constant)
      (quadHelperEntry s startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 x rest) =
    some (quadAfterHelperBeforeJump s (pcAfter startPC (quadBeforeJumpTemplate j constant))
      returnPC (quadWorking s x j p0 p1 p2 p3 M0 M1 M2 M3 constant) rest) := by
  interval_cases j

  · exact QuadRawTrace0.runInstrSeq_template s startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 constant x rest hstack hrun hactive hp0 hp1 hp2 hp3
  · exact QuadRawTrace1.runInstrSeq_template s startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 constant x rest hstack hrun hactive hp0 hp1 hp2 hp3
  · exact QuadRawTrace2.runInstrSeq_template s startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 constant x rest hstack hrun hactive hp0 hp1 hp2 hp3
  · exact QuadRawTrace3.runInstrSeq_template s startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 constant x rest hstack hrun hactive hp0 hp1 hp2 hp3
  · exact QuadRawTrace4.runInstrSeq_template s startPC p0 p1 p2 p3 returnPC M0 M1 M2 M3 constant x rest hstack hrun hactive hp0 hp1 hp2 hp3

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRawTrace
