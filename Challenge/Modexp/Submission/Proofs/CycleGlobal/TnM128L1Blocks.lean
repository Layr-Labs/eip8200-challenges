import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Suffix
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheHeadTrace
import Challenge.Modexp.Submission.Proofs.CycleGlobal.TnCacheExitTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace CycleSubmission.Global.Fast.TnM128L1Blocks
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast

def private3 : Block CycleSubmission.Artifact.artifact .Osaka 3809 TnCacheL1Suffix.privateProgram3 :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2942 89 3809 TnCacheL1Suffix.privateProgram3
    (by decide) (by rfl) (by rfl) (by decide)


def head4 : Block CycleSubmission.Artifact.artifact .Osaka 3775 (TnCacheHeadTrace.programC 2208) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2913 29 3775 (TnCacheHeadTrace.programC 2208)
    (by decide) (by rfl) (by rfl) (by decide)


def guard : Block CycleSubmission.Artifact.artifact .Osaka 3414 (TnCacheExitTrace.normalGuard) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2661 5 3414 (TnCacheExitTrace.normalGuard)
    (by decide) (by rfl) (by rfl) (by decide)


def drop : Block CycleSubmission.Artifact.artifact .Osaka 3428 (TnCacheExitTrace.drop) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2669 14 3428 (TnCacheExitTrace.drop)
    (by decide) (by rfl) (by rfl) (by decide)

end CycleSubmission.Global.Fast.TnM128L1Blocks
