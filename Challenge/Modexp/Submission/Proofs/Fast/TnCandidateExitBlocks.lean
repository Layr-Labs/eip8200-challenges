import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheExitTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateExitBlocks
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast TnCandidateArtifact

def guard : Block submissionArtifact .Osaka 4297 TnCacheExitTrace.normalGuard :=
  WindowTwentyOneSlice.block allWellFormed 3256 5 4297 TnCacheExitTrace.normalGuard
    (by decide) (by rfl) (by rfl) (by decide)

def drop : Block submissionArtifact .Osaka 4306 TnCacheExitTrace.drop :=
  WindowTwentyOneSlice.block allWellFormed 3261 14 4306 TnCacheExitTrace.drop
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateExitBlocks
