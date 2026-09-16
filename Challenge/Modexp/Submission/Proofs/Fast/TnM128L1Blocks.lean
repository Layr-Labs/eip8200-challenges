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

def common0 : Block submissionArtifact .Osaka 3646 (TnCacheL1Suffix.program 0) :=
  WindowTwentyOneSlice.block allWellFormed 2733 1 3646 (TnCacheL1Suffix.program 0)
    (by decide) (by rfl) (by rfl) (by decide)

def common1 : Block submissionArtifact .Osaka 3609 (TnCacheL1Suffix.program 1) :=
  WindowTwentyOneSlice.block allWellFormed 2702 32 3609 (TnCacheL1Suffix.program 1)
    (by decide) (by rfl) (by rfl) (by decide)

def common2 : Block submissionArtifact .Osaka 3572 (TnCacheL1Suffix.program 2) :=
  WindowTwentyOneSlice.block allWellFormed 2671 63 3572 (TnCacheL1Suffix.program 2)
    (by decide) (by rfl) (by rfl) (by decide)

def common3 : Block submissionArtifact .Osaka 3535 (TnCacheL1Suffix.program 3) :=
  WindowTwentyOneSlice.block allWellFormed 2640 94 3535 (TnCacheL1Suffix.program 3)
    (by decide) (by rfl) (by rfl) (by decide)

def common4 : Block submissionArtifact .Osaka 3498 (TnCacheL1Suffix.program 4) :=
  WindowTwentyOneSlice.block allWellFormed 2609 125 3498 (TnCacheL1Suffix.program 4)
    (by decide) (by rfl) (by rfl) (by decide)

def common5 : Block submissionArtifact .Osaka 3461 (TnCacheL1Suffix.program 5) :=
  WindowTwentyOneSlice.block allWellFormed 2578 156 3461 (TnCacheL1Suffix.program 5)
    (by decide) (by rfl) (by rfl) (by decide)

def common6 : Block submissionArtifact .Osaka 3424 (TnCacheL1Suffix.program 6) :=
  WindowTwentyOneSlice.block allWellFormed 2547 187 3424 (TnCacheL1Suffix.program 6)
    (by decide) (by rfl) (by rfl) (by decide)

def common7 : Block submissionArtifact .Osaka 3387 (TnCacheL1Suffix.program 7) :=
  WindowTwentyOneSlice.block allWellFormed 2516 218 3387 (TnCacheL1Suffix.program 7)
    (by decide) (by rfl) (by rfl) (by decide)

def private0 : Block submissionArtifact .Osaka 5290 (TnCacheL1Suffix.program 0) :=
  WindowTwentyOneSlice.block allWellFormed 4052 1 5290 (TnCacheL1Suffix.program 0)
    (by decide) (by rfl) (by rfl) (by decide)

def private1 : Block submissionArtifact .Osaka 5253 (TnCacheL1Suffix.program 1) :=
  WindowTwentyOneSlice.block allWellFormed 4021 32 5253 (TnCacheL1Suffix.program 1)
    (by decide) (by rfl) (by rfl) (by decide)

def private2 : Block submissionArtifact .Osaka 5216 (TnCacheL1Suffix.program 2) :=
  WindowTwentyOneSlice.block allWellFormed 3990 63 5216 (TnCacheL1Suffix.program 2)
    (by decide) (by rfl) (by rfl) (by decide)

def private3 : Block submissionArtifact .Osaka 5179 (TnCacheL1Suffix.program 3) :=
  WindowTwentyOneSlice.block allWellFormed 3959 94 5179 (TnCacheL1Suffix.program 3)
    (by decide) (by rfl) (by rfl) (by decide)

def head : Block submissionArtifact .Osaka 3358 (TnCacheHeadTrace.program) :=
  WindowTwentyOneSlice.block allWellFormed 2487 29 3358 (TnCacheHeadTrace.program)
    (by decide) (by rfl) (by rfl) (by decide)

def guard : Block submissionArtifact .Osaka 3968 (TnCacheExitTrace.normalGuard) :=
  WindowTwentyOneSlice.block allWellFormed 2979 5 3968 (TnCacheExitTrace.normalGuard)
    (by decide) (by rfl) (by rfl) (by decide)

def drop : Block submissionArtifact .Osaka 3977 (TnCacheExitTrace.drop) :=
  WindowTwentyOneSlice.block allWellFormed 2984 14 3977 (TnCacheExitTrace.drop)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Blocks
