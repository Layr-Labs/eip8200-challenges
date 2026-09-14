import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheHeadTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateHeadBlock
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast TnCandidateArtifact

def head : Block submissionArtifact .Osaka 3711 TnCacheHeadTrace.program :=
  WindowTwentyOneSlice.block allWellFormed 2769 29 3711 TnCacheHeadTrace.program
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateHeadBlock
