import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Branch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardEarly

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Entry

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan

/-- The merged classifier deleted the dedicated 376-byte entry, so a 376-byte input
reaches the scan by the SAME two steps a 1000-byte one uses.  Both are already
proved: `run_size_match_256` for the classifier, `gasSteps_checkEarly` for the
first-word test. -/
def gasSteps_hit (input : ByteArray) (hsize : input.size = 376)
    (href : KnownInputCompactState.referenceWord input ≠ KnownInputData.fullWord) :
    GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input) :=
  (Execution.gasSteps_start input).trans
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
        (DirectGuard.sizeDispatchPath input) (by rfl) (by rfl)
        (DirectGuard.run_size_match_256 input hsize) (by rfl)
        deployAddress_not_precompile).trans
      (DirectGuard.gasSteps_checkEarly input href))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Entry
