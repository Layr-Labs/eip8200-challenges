import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Suffix
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateL1Blocks
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast TnCandidateArtifact

def suffix0 : Block submissionArtifact .Osaka 3999 (TnCacheL1Suffix.program 0) :=
  WindowTwentyOneSlice.block allWellFormed 3004 1 3999 (TnCacheL1Suffix.program 0)
    (by decide) (by rfl) (by rfl) (by decide)

def suffix1 : Block submissionArtifact .Osaka 3962 (TnCacheL1Suffix.program 1) :=
  WindowTwentyOneSlice.block allWellFormed 2973 32 3962 (TnCacheL1Suffix.program 1)
    (by decide) (by rfl) (by rfl) (by decide)

def suffix2 : Block submissionArtifact .Osaka 3925 (TnCacheL1Suffix.program 2) :=
  WindowTwentyOneSlice.block allWellFormed 2942 63 3925 (TnCacheL1Suffix.program 2)
    (by decide) (by rfl) (by rfl) (by decide)

def suffix3 : Block submissionArtifact .Osaka 3888 (TnCacheL1Suffix.program 3) :=
  WindowTwentyOneSlice.block allWellFormed 2911 94 3888 (TnCacheL1Suffix.program 3)
    (by decide) (by rfl) (by rfl) (by decide)

def suffix4 : Block submissionArtifact .Osaka 3851 (TnCacheL1Suffix.program 4) :=
  WindowTwentyOneSlice.block allWellFormed 2880 125 3851 (TnCacheL1Suffix.program 4)
    (by decide) (by rfl) (by rfl) (by decide)

def suffix5 : Block submissionArtifact .Osaka 3814 (TnCacheL1Suffix.program 5) :=
  WindowTwentyOneSlice.block allWellFormed 2849 156 3814 (TnCacheL1Suffix.program 5)
    (by decide) (by rfl) (by rfl) (by decide)

def suffix6 : Block submissionArtifact .Osaka 3777 (TnCacheL1Suffix.program 6) :=
  WindowTwentyOneSlice.block allWellFormed 2818 187 3777 (TnCacheL1Suffix.program 6)
    (by decide) (by rfl) (by rfl) (by decide)

def suffix7 : Block submissionArtifact .Osaka 3740 (TnCacheL1Suffix.program 7) :=
  WindowTwentyOneSlice.block allWellFormed 2787 218 3740 (TnCacheL1Suffix.program 7)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateL1Blocks
