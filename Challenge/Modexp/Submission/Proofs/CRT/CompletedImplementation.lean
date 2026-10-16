import Challenge.Modexp.Submission.Proofs.CRT.CallerBridge
import Challenge.Modexp.Submission.Proofs.CRT.CRTLoopComplete
set_option warningAsError true

namespace HistoricalSearch.CompletedImplementation
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast

/-- The replacement loop's complete public subroutine contract. Its internal
trace is the concrete, checked instruction execution and branch induction. -/
noncomputable def implementation (s : State) (bsize N mi : Nat)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hact : 88≤s.activeWords.toNat) (hcds : s.executionEnv.calldata.size<2^256)
    (hodd : N%2=1) (hmi : mi<2^256) (hmiA : (N%Limbs.radix*mi+1)%2^256=0) :
    CRTLoopInterface.Implementation s bsize N mi :=
  CallerBridge.implementation s bsize N mi env hact hcds hodd hmi hmiA
    (fun minv n k mem f A hcap h =>
      CRTLoopComplete.run s minv n N env hact hcds k mem f A hcap h)

#print axioms implementation
end HistoricalSearch.CompletedImplementation
