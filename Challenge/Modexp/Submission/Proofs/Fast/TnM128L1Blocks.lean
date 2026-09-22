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

def common0 : Block submissionArtifact .Osaka 3821 (TnCacheL1Suffix.program 0) :=
  WindowTwentyOneSlice.block allWellFormed 3067 1 3821 (TnCacheL1Suffix.program 0)
    (by decide) (by rfl) (by rfl) (by decide)

def common1 : Block submissionArtifact .Osaka 3784 (TnCacheL1Suffix.program 1) :=
  WindowTwentyOneSlice.block allWellFormed 3036 32 3784 (TnCacheL1Suffix.program 1)
    (by decide) (by rfl) (by rfl) (by decide)

def common2 : Block submissionArtifact .Osaka 3747 (TnCacheL1Suffix.program 2) :=
  WindowTwentyOneSlice.block allWellFormed 3005 63 3747 (TnCacheL1Suffix.program 2)
    (by decide) (by rfl) (by rfl) (by decide)

def common3 : Block submissionArtifact .Osaka 3710 (TnCacheL1Suffix.program 3) :=
  WindowTwentyOneSlice.block allWellFormed 2974 94 3710 (TnCacheL1Suffix.program 3)
    (by decide) (by rfl) (by rfl) (by decide)

def common4 : Block submissionArtifact .Osaka 3673 (TnCacheL1Suffix.program 4) :=
  WindowTwentyOneSlice.block allWellFormed 2943 125 3673 (TnCacheL1Suffix.program 4)
    (by decide) (by rfl) (by rfl) (by decide)

def common5 : Block submissionArtifact .Osaka 3636 (TnCacheL1Suffix.program 5) :=
  WindowTwentyOneSlice.block allWellFormed 2912 156 3636 (TnCacheL1Suffix.program 5)
    (by decide) (by rfl) (by rfl) (by decide)

def common6 : Block submissionArtifact .Osaka 3599 (TnCacheL1Suffix.program 6) :=
  WindowTwentyOneSlice.block allWellFormed 2881 187 3599 (TnCacheL1Suffix.program 6)
    (by decide) (by rfl) (by rfl) (by decide)

def common7 : Block submissionArtifact .Osaka 3562 (TnCacheL1Suffix.program 7) :=
  WindowTwentyOneSlice.block allWellFormed 2850 218 3562 (TnCacheL1Suffix.program 7)
    (by decide) (by rfl) (by rfl) (by decide)

def private0 : Block submissionArtifact .Osaka 5420 (TnCacheL1Suffix.program 0) :=
  WindowTwentyOneSlice.block allWellFormed 4370 1 5420 (TnCacheL1Suffix.program 0)
    (by decide) (by rfl) (by rfl) (by decide)

def private1 : Block submissionArtifact .Osaka 5383 (TnCacheL1Suffix.program 1) :=
  WindowTwentyOneSlice.block allWellFormed 4339 32 5383 (TnCacheL1Suffix.program 1)
    (by decide) (by rfl) (by rfl) (by decide)

def private2 : Block submissionArtifact .Osaka 5346 (TnCacheL1Suffix.program 2) :=
  WindowTwentyOneSlice.block allWellFormed 4308 63 5346 (TnCacheL1Suffix.program 2)
    (by decide) (by rfl) (by rfl) (by decide)

def private3 : Block submissionArtifact .Osaka 5309 (TnCacheL1Suffix.program 3) :=
  WindowTwentyOneSlice.block allWellFormed 4277 94 5309 (TnCacheL1Suffix.program 3)
    (by decide) (by rfl) (by rfl) (by decide)

def head : Block submissionArtifact .Osaka 3533 (TnCacheHeadTrace.program) :=
  WindowTwentyOneSlice.block allWellFormed 2821 29 3533 (TnCacheHeadTrace.program)
    (by decide) (by rfl) (by rfl) (by decide)

def guard : Block submissionArtifact .Osaka 4133 (TnCacheExitTrace.normalGuard) :=
  WindowTwentyOneSlice.block allWellFormed 3313 5 4133 (TnCacheExitTrace.normalGuard)
    (by decide) (by rfl) (by rfl) (by decide)

def drop : Block submissionArtifact .Osaka 4142 (TnCacheExitTrace.drop) :=
  WindowTwentyOneSlice.block allWellFormed 3318 14 4142 (TnCacheExitTrace.drop)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Blocks
