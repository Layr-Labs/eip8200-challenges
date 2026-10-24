import Challenge.Modexp.Submission.Proofs.CRT.PureSquareMemory
import Challenge.Modexp.Submission.Proofs.Fast.CRTLoopInterface
set_option warningAsError true

namespace HistoricalSearch.PureSquareInterface
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

/-- Concrete value/memory interface; execution is supplied separately by the
retained-loop trace proof. -/
def model (s : State) : CRTLoopInterface.SquareMemory where
  memory := PureSquareMemory.memory s
  low := PureSquareMemory.low s
  inverse := PureSquareMemory.inverse s
  value := PureSquareMemory.value s

#print axioms model
end HistoricalSearch.PureSquareInterface
