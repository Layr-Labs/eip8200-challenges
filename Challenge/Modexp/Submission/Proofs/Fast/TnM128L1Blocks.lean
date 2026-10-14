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

def common0 : Block submissionArtifact .Osaka 3626 (TnCacheL1Suffix.program 0) :=
  WindowTwentyOneSlice.block allWellFormed 2839 1 3626 (TnCacheL1Suffix.program 0)
    (by decide) (by rfl) (by rfl) (by decide)

def common1 : Block submissionArtifact .Osaka 3589 (TnCacheL1Suffix.program 1) :=
  WindowTwentyOneSlice.block allWellFormed 2808 32 3589 (TnCacheL1Suffix.program 1)
    (by decide) (by rfl) (by rfl) (by decide)

def common2 : Block submissionArtifact .Osaka 3552 (TnCacheL1Suffix.program 2) :=
  WindowTwentyOneSlice.block allWellFormed 2777 63 3552 (TnCacheL1Suffix.program 2)
    (by decide) (by rfl) (by rfl) (by decide)

def common3 : Block submissionArtifact .Osaka 3515 (TnCacheL1Suffix.program 3) :=
  WindowTwentyOneSlice.block allWellFormed 2746 94 3515 (TnCacheL1Suffix.program 3)
    (by decide) (by rfl) (by rfl) (by decide)

def common4 : Block submissionArtifact .Osaka 3478 (TnCacheL1Suffix.program 4) :=
  WindowTwentyOneSlice.block allWellFormed 2715 125 3478 (TnCacheL1Suffix.program 4)
    (by decide) (by rfl) (by rfl) (by decide)

def common5 : Block submissionArtifact .Osaka 3441 (TnCacheL1Suffix.program 5) :=
  WindowTwentyOneSlice.block allWellFormed 2684 156 3441 (TnCacheL1Suffix.program 5)
    (by decide) (by rfl) (by rfl) (by decide)

def common6 : Block submissionArtifact .Osaka 3404 (TnCacheL1Suffix.program 6) :=
  WindowTwentyOneSlice.block allWellFormed 2653 187 3404 (TnCacheL1Suffix.program 6)
    (by decide) (by rfl) (by rfl) (by decide)

def common7 : Block submissionArtifact .Osaka 3367 (TnCacheL1Suffix.program 7) :=
  WindowTwentyOneSlice.block allWellFormed 2622 218 3367 (TnCacheL1Suffix.program 7)
    (by decide) (by rfl) (by rfl) (by decide)

def private3 : Block submissionArtifact .Osaka 5410 TnCacheL1Suffix.privateProgram3 :=
  WindowTwentyOneSlice.block allWellFormed 4324 91 5410 TnCacheL1Suffix.privateProgram3
    (by decide) (by rfl) (by rfl) (by decide)

def head : Block submissionArtifact .Osaka 3333 (TnCacheHeadTrace.programC 2336) :=
  WindowTwentyOneSlice.block allWellFormed 2593 29 3333 (TnCacheHeadTrace.programC 2336)
    (by decide) (by rfl) (by rfl) (by decide)

/-- The four-limb multiply row head (msplit's `m4` copy), falling into `private3`. -/
def head4 : Block submissionArtifact .Osaka 5376 (TnCacheHeadTrace.programC 2208) :=
  WindowTwentyOneSlice.block allWellFormed 4295 29 5376 (TnCacheHeadTrace.programC 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def guard : Block submissionArtifact .Osaka 3895 (TnCacheExitTrace.normalGuard) :=
  WindowTwentyOneSlice.block allWellFormed 3073 5 3895 (TnCacheExitTrace.normalGuard)
    (by decide) (by rfl) (by rfl) (by decide)

def drop : Block submissionArtifact .Osaka 3909 (TnCacheExitTrace.drop) :=
  WindowTwentyOneSlice.block allWellFormed 3081 14 3909 (TnCacheExitTrace.drop)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Blocks
