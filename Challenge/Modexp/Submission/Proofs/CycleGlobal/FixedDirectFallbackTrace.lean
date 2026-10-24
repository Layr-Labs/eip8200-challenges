import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PrefixPC
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FixedDirectValueTrace

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Bail from the fixed-exponent dispatcher

Every nonmatching exponent leaves the fast path with a jump to `modexpBig`
(pc 219) with the outer frame untouched.  The generic exponent loop is no longer reachable from here.
-/

namespace CycleSubmission.Global.FixedDirectFallbackTrace
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
open CycleSubmission.Global.FixedDirectPaths

/-- The misses jump straight to `modexpBig`: `bailState` is `bigCState`. -/
def gasSteps_bail (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) :
    Challenge.EvmProof.GasSteps
      (FixedDirectStates.bailState s memory n bsize esize msize)
      (FixedDirectStates.bigCState s memory n bsize esize msize) :=
  Challenge.EvmProof.GasSteps.refl _

end CycleSubmission.Global.FixedDirectFallbackTrace
