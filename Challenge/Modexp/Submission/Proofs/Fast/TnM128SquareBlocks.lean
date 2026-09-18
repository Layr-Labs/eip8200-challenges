import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquareTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareBlocks
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast TnM128CandidateArtifact

def blockA : Block submissionArtifact .Osaka 4268 TnCacheSquareTrace.programA :=
  WindowTwentyOneSlice.block allWellFormed 3389 6 4268 TnCacheSquareTrace.programA
    (by decide) (by rfl) (by rfl) (by decide)

def blockB : Block submissionArtifact .Osaka 4275 TnCacheSquareTrace.programB :=
  WindowTwentyOneSlice.block allWellFormed 3396 40 4275 TnCacheSquareTrace.programB
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareBlocks
