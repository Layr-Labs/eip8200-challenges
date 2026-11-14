import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Fallback
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.FixedRoute
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open FixedExponentRoute
theorem prepend {input : ByteArray} {start middle : State}
    (head : GasSteps start middle) (tail : Handled input middle) : Handled input start := by
  obtain ⟨final,⟨tr⟩,hd,hr⟩ := tail
  exact ⟨final,⟨head.trans tr⟩,hd,hr⟩
end CycleSubmission.Global.FixedRoute
