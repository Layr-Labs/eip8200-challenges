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

def common0 : Block submissionArtifact .Osaka 3831 (TnCacheL1Suffix.program 0) :=
  WindowTwentyOneSlice.block allWellFormed 3063 1 3831 (TnCacheL1Suffix.program 0)
    (by decide) (by rfl) (by rfl) (by decide)

def common1 : Block submissionArtifact .Osaka 3794 (TnCacheL1Suffix.program 1) :=
  WindowTwentyOneSlice.block allWellFormed 3032 32 3794 (TnCacheL1Suffix.program 1)
    (by decide) (by rfl) (by rfl) (by decide)

def common2 : Block submissionArtifact .Osaka 3757 (TnCacheL1Suffix.program 2) :=
  WindowTwentyOneSlice.block allWellFormed 3001 63 3757 (TnCacheL1Suffix.program 2)
    (by decide) (by rfl) (by rfl) (by decide)

def common3 : Block submissionArtifact .Osaka 3720 (TnCacheL1Suffix.program 3) :=
  WindowTwentyOneSlice.block allWellFormed 2970 94 3720 (TnCacheL1Suffix.program 3)
    (by decide) (by rfl) (by rfl) (by decide)

def common4 : Block submissionArtifact .Osaka 3683 (TnCacheL1Suffix.program 4) :=
  WindowTwentyOneSlice.block allWellFormed 2939 125 3683 (TnCacheL1Suffix.program 4)
    (by decide) (by rfl) (by rfl) (by decide)

def common5 : Block submissionArtifact .Osaka 3646 (TnCacheL1Suffix.program 5) :=
  WindowTwentyOneSlice.block allWellFormed 2908 156 3646 (TnCacheL1Suffix.program 5)
    (by decide) (by rfl) (by rfl) (by decide)

def common6 : Block submissionArtifact .Osaka 3609 (TnCacheL1Suffix.program 6) :=
  WindowTwentyOneSlice.block allWellFormed 2877 187 3609 (TnCacheL1Suffix.program 6)
    (by decide) (by rfl) (by rfl) (by decide)

def common7 : Block submissionArtifact .Osaka 3572 (TnCacheL1Suffix.program 7) :=
  WindowTwentyOneSlice.block allWellFormed 2846 218 3572 (TnCacheL1Suffix.program 7)
    (by decide) (by rfl) (by rfl) (by decide)

def private0 : Block submissionArtifact .Osaka 5430 (TnCacheL1Suffix.program 0) :=
  WindowTwentyOneSlice.block allWellFormed 4366 1 5430 (TnCacheL1Suffix.program 0)
    (by decide) (by rfl) (by rfl) (by decide)

def private1 : Block submissionArtifact .Osaka 5393 (TnCacheL1Suffix.program 1) :=
  WindowTwentyOneSlice.block allWellFormed 4335 32 5393 (TnCacheL1Suffix.program 1)
    (by decide) (by rfl) (by rfl) (by decide)

def private2 : Block submissionArtifact .Osaka 5356 (TnCacheL1Suffix.program 2) :=
  WindowTwentyOneSlice.block allWellFormed 4304 63 5356 (TnCacheL1Suffix.program 2)
    (by decide) (by rfl) (by rfl) (by decide)

def private3 : Block submissionArtifact .Osaka 5319 (TnCacheL1Suffix.program 3) :=
  WindowTwentyOneSlice.block allWellFormed 4273 94 5319 (TnCacheL1Suffix.program 3)
    (by decide) (by rfl) (by rfl) (by decide)

def head : Block submissionArtifact .Osaka 3543 (TnCacheHeadTrace.program) :=
  WindowTwentyOneSlice.block allWellFormed 2817 29 3543 (TnCacheHeadTrace.program)
    (by decide) (by rfl) (by rfl) (by decide)

def guard : Block submissionArtifact .Osaka 4143 (TnCacheExitTrace.normalGuard) :=
  WindowTwentyOneSlice.block allWellFormed 3309 5 4143 (TnCacheExitTrace.normalGuard)
    (by decide) (by rfl) (by rfl) (by decide)

def drop : Block submissionArtifact .Osaka 4152 (TnCacheExitTrace.drop) :=
  WindowTwentyOneSlice.block allWellFormed 3314 14 4152 (TnCacheExitTrace.drop)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Blocks
