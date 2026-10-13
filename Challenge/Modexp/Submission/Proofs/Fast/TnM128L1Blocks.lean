import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Suffix
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheHeadTrace
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheExitTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Blocks
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast TnM128CandidateArtifact

def common0 : Block submissionArtifact .Osaka 3849 (TnCacheL1Suffix.program 0) :=
  WindowTwentyOneSlice.block allWellFormed 3014 1 3849 (TnCacheL1Suffix.program 0)
    (by decide) (by rfl) (by rfl) (by decide)

def common1 : Block submissionArtifact .Osaka 3812 (TnCacheL1Suffix.program 1) :=
  WindowTwentyOneSlice.block allWellFormed 2983 32 3812 (TnCacheL1Suffix.program 1)
    (by decide) (by rfl) (by rfl) (by decide)

def common2 : Block submissionArtifact .Osaka 3775 (TnCacheL1Suffix.program 2) :=
  WindowTwentyOneSlice.block allWellFormed 2952 63 3775 (TnCacheL1Suffix.program 2)
    (by decide) (by rfl) (by rfl) (by decide)

def common3 : Block submissionArtifact .Osaka 3738 (TnCacheL1Suffix.program 3) :=
  WindowTwentyOneSlice.block allWellFormed 2921 94 3738 (TnCacheL1Suffix.program 3)
    (by decide) (by rfl) (by rfl) (by decide)

def common4 : Block submissionArtifact .Osaka 3701 (TnCacheL1Suffix.program 4) :=
  WindowTwentyOneSlice.block allWellFormed 2890 125 3701 (TnCacheL1Suffix.program 4)
    (by decide) (by rfl) (by rfl) (by decide)

def common5 : Block submissionArtifact .Osaka 3664 (TnCacheL1Suffix.program 5) :=
  WindowTwentyOneSlice.block allWellFormed 2859 156 3664 (TnCacheL1Suffix.program 5)
    (by decide) (by rfl) (by rfl) (by decide)

def common6 : Block submissionArtifact .Osaka 3627 (TnCacheL1Suffix.program 6) :=
  WindowTwentyOneSlice.block allWellFormed 2828 187 3627 (TnCacheL1Suffix.program 6)
    (by decide) (by rfl) (by rfl) (by decide)

def common7 : Block submissionArtifact .Osaka 3590 (TnCacheL1Suffix.program 7) :=
  WindowTwentyOneSlice.block allWellFormed 2797 218 3590 (TnCacheL1Suffix.program 7)
    (by decide) (by rfl) (by rfl) (by decide)

def private3 : Block submissionArtifact .Osaka 5366 TnCacheL1Suffix.privateProgram3 :=
  WindowTwentyOneSlice.block allWellFormed 4258 91 5366 TnCacheL1Suffix.privateProgram3
    (by decide) (by rfl) (by rfl) (by decide)

def head : Block submissionArtifact .Osaka 3561 (TnCacheHeadTrace.program) :=
  WindowTwentyOneSlice.block allWellFormed 2768 29 3561 (TnCacheHeadTrace.program)
    (by decide) (by rfl) (by rfl) (by decide)

def guard : Block submissionArtifact .Osaka 4157 (TnCacheExitTrace.normalGuard) :=
  WindowTwentyOneSlice.block allWellFormed 3256 5 4157 (TnCacheExitTrace.normalGuard)
    (by decide) (by rfl) (by rfl) (by decide)

def drop : Block submissionArtifact .Osaka 4166 (TnCacheExitTrace.drop) :=
  WindowTwentyOneSlice.block allWellFormed 3261 14 4166 (TnCacheExitTrace.drop)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Blocks
