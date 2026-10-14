import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnMod128Chain
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheReductionTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast TnM128CandidateArtifact

def l2Eight : Block submissionArtifact .Osaka 3650 (TnMod128Chain.fullProgram 8) :=
  WindowTwentyOneSlice.block allWellFormed 2859 199 3650 (TnMod128Chain.fullProgram 8)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Four : Block submissionArtifact .Osaka 3779 (TnMod128Chain.fullProgram 4) :=
  WindowTwentyOneSlice.block allWellFormed 2972 86 3779 (TnMod128Chain.fullProgram 4)
    (by decide) (by rfl) (by rfl) (by decide)

def cachedCell : Block submissionArtifact .Osaka 3715 (TnMod128Trace.program) :=
  WindowTwentyOneSlice.block allWellFormed 2916 28 3715 (TnMod128Trace.program)
    (by decide) (by rfl) (by rfl) (by decide)

def middle8 : Block submissionArtifact .Osaka 3627 (TnCacheRowTrace.middle8) :=
  WindowTwentyOneSlice.block allWellFormed 2840 19 3627 (TnCacheRowTrace.middle8)
    (by decide) (by rfl) (by rfl) (by decide)

def middleCopy : Block submissionArtifact .Osaka 5519 (TnCacheRowTrace.middle4 ++ [.push 2 3779, .op .JUMP]) :=
  WindowTwentyOneSlice.block allWellFormed 4415 21 5519 (TnCacheRowTrace.middle4 ++ [.push 2 3779, .op .JUMP])
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block submissionArtifact .Osaka 3877 (TnCacheRowTrace.tail) :=
  WindowTwentyOneSlice.block allWellFormed 3058 15 3877 (TnCacheRowTrace.tail)
    (by decide) (by rfl) (by rfl) (by decide)

def flush : Block submissionArtifact .Osaka 3904 (TnCacheFrameOps.flush13) :=
  WindowTwentyOneSlice.block allWellFormed 3078 3 3904 (TnCacheFrameOps.flush13)
    (by decide) (by rfl) (by rfl) (by decide)

def afterSquareReset : Block submissionArtifact .Osaka 3276 (TnCacheFrameOps.reset13) :=
  WindowTwentyOneSlice.block allWellFormed 2556 3 3276 (TnCacheFrameOps.reset13)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks
