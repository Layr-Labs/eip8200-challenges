import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheReductionTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateBlocks
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open TnCandidateArtifact

def l2Eight : Block submissionArtifact .Osaka 4023 (TnCacheL2Chain.fullProgram 8) :=
  WindowTwentyOneSlice.block allWellFormed 3028 207 4023 (TnCacheL2Chain.fullProgram 8)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Four : Block submissionArtifact .Osaka 4171 (TnCacheL2Chain.fullProgram 4) :=
  WindowTwentyOneSlice.block allWellFormed 3147 88 4171 (TnCacheL2Chain.fullProgram 4)
    (by decide) (by rfl) (by rfl) (by decide)

def middle : Block submissionArtifact .Osaka 4000 (TnCacheRowTrace.middle ++ TnCacheReductionTrace.dispatch) :=
  WindowTwentyOneSlice.block allWellFormed 3005 23 4000 (TnCacheRowTrace.middle ++ TnCacheReductionTrace.dispatch)
    (by decide) (by rfl) (by rfl) (by decide)

def tailShort : Block submissionArtifact .Osaka 4271 (TnCacheRowTrace.tailShort) :=
  WindowTwentyOneSlice.block allWellFormed 3235 18 4271 (TnCacheRowTrace.tailShort)
    (by decide) (by rfl) (by rfl) (by decide)

def flush : Block submissionArtifact .Osaka 4292 (TnCacheFrameOps.flush) :=
  WindowTwentyOneSlice.block allWellFormed 3253 3 4292 (TnCacheFrameOps.flush)
    (by decide) (by rfl) (by rfl) (by decide)

def afterSquareReset : Block submissionArtifact .Osaka 3658 (TnCacheFrameOps.reset) :=
  WindowTwentyOneSlice.block allWellFormed 2722 3 3658 (TnCacheFrameOps.reset)
    (by decide) (by rfl) (by rfl) (by decide)

def againReset : Block submissionArtifact .Osaka 4419 (TnCacheFrameOps.reset) :=
  WindowTwentyOneSlice.block allWellFormed 3335 3 4419 (TnCacheFrameOps.reset)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateBlocks
