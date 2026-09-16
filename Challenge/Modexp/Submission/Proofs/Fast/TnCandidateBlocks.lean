import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheReductionTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast TnCandidateArtifact

def l2Eight : Block submissionArtifact .Osaka 3662 (TnCacheL2Chain.fullProgram 8) :=
  WindowTwentyOneSlice.block allWellFormed 2750 207 3662 (TnCacheL2Chain.fullProgram 8)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Four : Block submissionArtifact .Osaka 3810 (TnCacheL2Chain.fullProgram 4) :=
  WindowTwentyOneSlice.block allWellFormed 2869 88 3810 (TnCacheL2Chain.fullProgram 4)
    (by decide) (by rfl) (by rfl) (by decide)

def middle : Block submissionArtifact .Osaka 3643 (TnCacheRowTrace.middle) :=
  WindowTwentyOneSlice.block allWellFormed 2731 19 3643 (TnCacheRowTrace.middle)
    (by decide) (by rfl) (by rfl) (by decide)

def middleCopy : Block submissionArtifact .Osaka 5287 (TnCacheRowTrace.middle ++ [.push 2 3810, .op .JUMP]) :=
  WindowTwentyOneSlice.block allWellFormed 4051 21 5287 (TnCacheRowTrace.middle ++ [.push 2 3810, .op .JUMP])
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block submissionArtifact .Osaka 3910 (TnCacheRowTrace.tail) :=
  WindowTwentyOneSlice.block allWellFormed 2957 17 3910 (TnCacheRowTrace.tail)
    (by decide) (by rfl) (by rfl) (by decide)

def flush : Block submissionArtifact .Osaka 3961 (TnCacheFrameOps.flush) :=
  WindowTwentyOneSlice.block allWellFormed 2974 3 3961 (TnCacheFrameOps.flush)
    (by decide) (by rfl) (by rfl) (by decide)

def afterSquareReset : Block submissionArtifact .Osaka 3301 (TnCacheFrameOps.reset) :=
  WindowTwentyOneSlice.block allWellFormed 2449 3 3301 (TnCacheFrameOps.reset)
    (by decide) (by rfl) (by rfl) (by decide)

def againReset : Block submissionArtifact .Osaka 4075 (TnCacheFrameOps.reset) :=
  WindowTwentyOneSlice.block allWellFormed 3047 3 4075 (TnCacheFrameOps.reset)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateBlocks
