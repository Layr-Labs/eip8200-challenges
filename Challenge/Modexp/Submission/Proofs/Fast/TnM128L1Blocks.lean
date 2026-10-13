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

def common0 : Block submissionArtifact .Osaka 3838 (TnCacheL1Suffix.program 0) :=
  WindowTwentyOneSlice.block allWellFormed 3001 1 3838 (TnCacheL1Suffix.program 0)
    (by decide) (by rfl) (by rfl) (by decide)

def common1 : Block submissionArtifact .Osaka 3801 (TnCacheL1Suffix.program 1) :=
  WindowTwentyOneSlice.block allWellFormed 2970 32 3801 (TnCacheL1Suffix.program 1)
    (by decide) (by rfl) (by rfl) (by decide)

def common2 : Block submissionArtifact .Osaka 3764 (TnCacheL1Suffix.program 2) :=
  WindowTwentyOneSlice.block allWellFormed 2939 63 3764 (TnCacheL1Suffix.program 2)
    (by decide) (by rfl) (by rfl) (by decide)

def common3 : Block submissionArtifact .Osaka 3727 (TnCacheL1Suffix.program 3) :=
  WindowTwentyOneSlice.block allWellFormed 2908 94 3727 (TnCacheL1Suffix.program 3)
    (by decide) (by rfl) (by rfl) (by decide)

def common4 : Block submissionArtifact .Osaka 3690 (TnCacheL1Suffix.program 4) :=
  WindowTwentyOneSlice.block allWellFormed 2877 125 3690 (TnCacheL1Suffix.program 4)
    (by decide) (by rfl) (by rfl) (by decide)

def common5 : Block submissionArtifact .Osaka 3653 (TnCacheL1Suffix.program 5) :=
  WindowTwentyOneSlice.block allWellFormed 2846 156 3653 (TnCacheL1Suffix.program 5)
    (by decide) (by rfl) (by rfl) (by decide)

def common6 : Block submissionArtifact .Osaka 3616 (TnCacheL1Suffix.program 6) :=
  WindowTwentyOneSlice.block allWellFormed 2815 187 3616 (TnCacheL1Suffix.program 6)
    (by decide) (by rfl) (by rfl) (by decide)

def common7 : Block submissionArtifact .Osaka 3579 (TnCacheL1Suffix.program 7) :=
  WindowTwentyOneSlice.block allWellFormed 2784 218 3579 (TnCacheL1Suffix.program 7)
    (by decide) (by rfl) (by rfl) (by decide)

def private3 : Block submissionArtifact .Osaka 5373 TnCacheL1Suffix.privateProgram3 :=
  WindowTwentyOneSlice.block allWellFormed 4232 91 5373 TnCacheL1Suffix.privateProgram3
    (by decide) (by rfl) (by rfl) (by decide)

def head : Block submissionArtifact .Osaka 3545 (TnCacheHeadTrace.programC 2336) :=
  WindowTwentyOneSlice.block allWellFormed 2755 29 3545 (TnCacheHeadTrace.programC 2336)
    (by decide) (by rfl) (by rfl) (by decide)

/-- The four-limb multiply row head (msplit's `m4` copy), falling into `private3`. -/
def head4 : Block submissionArtifact .Osaka 5339 (TnCacheHeadTrace.programC 2208) :=
  WindowTwentyOneSlice.block allWellFormed 4203 29 5339 (TnCacheHeadTrace.programC 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def guard : Block submissionArtifact .Osaka 4138 (TnCacheExitTrace.normalGuard) :=
  WindowTwentyOneSlice.block allWellFormed 3235 5 4138 (TnCacheExitTrace.normalGuard)
    (by decide) (by rfl) (by rfl) (by decide)

def drop : Block submissionArtifact .Osaka 4152 (TnCacheExitTrace.drop) :=
  WindowTwentyOneSlice.block allWellFormed 3243 14 4152 (TnCacheExitTrace.drop)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128L1Blocks
