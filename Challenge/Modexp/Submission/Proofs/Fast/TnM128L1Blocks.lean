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

def common0 : Block submissionArtifact .Osaka 3606 (TnCacheL1Suffix.program 0) :=
  WindowTwentyOneSlice.block allWellFormed 2816 1 3606 (TnCacheL1Suffix.program 0)
    (by decide) (by rfl) (by rfl) (by decide)

def common1 : Block submissionArtifact .Osaka 3569 (TnCacheL1Suffix.program 1) :=
  WindowTwentyOneSlice.block allWellFormed 2785 32 3569 (TnCacheL1Suffix.program 1)
    (by decide) (by rfl) (by rfl) (by decide)

def common2 : Block submissionArtifact .Osaka 3532 (TnCacheL1Suffix.program 2) :=
  WindowTwentyOneSlice.block allWellFormed 2754 63 3532 (TnCacheL1Suffix.program 2)
    (by decide) (by rfl) (by rfl) (by decide)

def common3 : Block submissionArtifact .Osaka 3495 (TnCacheL1Suffix.program 3) :=
  WindowTwentyOneSlice.block allWellFormed 2723 94 3495 (TnCacheL1Suffix.program 3)
    (by decide) (by rfl) (by rfl) (by decide)

def common4 : Block submissionArtifact .Osaka 3458 (TnCacheL1Suffix.program 4) :=
  WindowTwentyOneSlice.block allWellFormed 2692 125 3458 (TnCacheL1Suffix.program 4)
    (by decide) (by rfl) (by rfl) (by decide)

def common5 : Block submissionArtifact .Osaka 3421 (TnCacheL1Suffix.program 5) :=
  WindowTwentyOneSlice.block allWellFormed 2661 156 3421 (TnCacheL1Suffix.program 5)
    (by decide) (by rfl) (by rfl) (by decide)

def common6 : Block submissionArtifact .Osaka 3384 (TnCacheL1Suffix.program 6) :=
  WindowTwentyOneSlice.block allWellFormed 2630 187 3384 (TnCacheL1Suffix.program 6)
    (by decide) (by rfl) (by rfl) (by decide)

def common7 : Block submissionArtifact .Osaka 3347 (TnCacheL1Suffix.program 7) :=
  WindowTwentyOneSlice.block allWellFormed 2599 218 3347 (TnCacheL1Suffix.program 7)
    (by decide) (by rfl) (by rfl) (by decide)

def private3 : Block submissionArtifact .Osaka 5387 TnCacheL1Suffix.privateProgram3 :=
  WindowTwentyOneSlice.block allWellFormed 4300 89 5387 TnCacheL1Suffix.privateProgram3
    (by decide) (by rfl) (by rfl) (by decide)

def head : Block submissionArtifact .Osaka 3313 (TnCacheHeadTrace.programC 2336) :=
  WindowTwentyOneSlice.block allWellFormed 2570 29 3313 (TnCacheHeadTrace.programC 2336)
    (by decide) (by rfl) (by rfl) (by decide)

/-- The four-limb multiply row head (msplit's `m4` copy), falling into `private3`. -/
def head4 : Block submissionArtifact .Osaka 5353 (TnCacheHeadTrace.programC 2208) :=
  WindowTwentyOneSlice.block allWellFormed 4271 29 5353 (TnCacheHeadTrace.programC 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def guard : Block submissionArtifact .Osaka 3874 (TnCacheExitTrace.normalGuard) :=
  WindowTwentyOneSlice.block allWellFormed 3049 5 3874 (TnCacheExitTrace.normalGuard)
    (by decide) (by rfl) (by rfl) (by decide)

def drop : Block submissionArtifact .Osaka 3888 (TnCacheExitTrace.drop) :=
  WindowTwentyOneSlice.block allWellFormed 3057 14 3888 (TnCacheExitTrace.drop)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Blocks
