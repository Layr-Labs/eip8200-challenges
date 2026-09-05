import Challenge.Ripemd160.Submission.H39Memo.A1000Jumps

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.H39Memo.A1000
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

theorem run_singleton (loc : Located) (s : State) :
    Stepper.runLocatedBlock [loc] s = Stepper.runLocated loc s := by
  unfold Stepper.runLocatedBlock
  cases Stepper.runLocated loc s <;> rfl

end Challenge.Ripemd160.Submission.H39Memo.A1000

