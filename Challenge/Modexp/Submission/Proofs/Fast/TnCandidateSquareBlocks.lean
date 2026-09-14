import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquareTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareBlocks
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast TnCandidateArtifact

def blockA : Block submissionArtifact .Osaka 4471 TnCacheSquareTrace.programA :=
  WindowTwentyOneSlice.block allWellFormed 3388 6 4471 TnCacheSquareTrace.programA
    (by decide) (by rfl) (by rfl) (by decide)

def blockB : Block submissionArtifact .Osaka 4478 TnCacheSquareTrace.programB :=
  WindowTwentyOneSlice.block allWellFormed 3395 40 4478 TnCacheSquareTrace.programB
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSquareBlocks
