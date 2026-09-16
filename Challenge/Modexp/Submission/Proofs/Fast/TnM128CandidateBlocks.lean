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

def l2Eight : Block submissionArtifact .Osaka 3666 (TnMod128Chain.fullProgram 8) :=
  WindowTwentyOneSlice.block allWellFormed 2753 206 3666 (TnMod128Chain.fullProgram 8)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Four : Block submissionArtifact .Osaka 3812 (TnMod128Chain.fullProgram 4) :=
  WindowTwentyOneSlice.block allWellFormed 2871 88 3812 (TnMod128Chain.fullProgram 4)
    (by decide) (by rfl) (by rfl) (by decide)

def cachedCell : Block submissionArtifact .Osaka 3746 (TnMod128Trace.program) :=
  WindowTwentyOneSlice.block allWellFormed 2814 29 3746 (TnMod128Trace.program)
    (by decide) (by rfl) (by rfl) (by decide)

def middle : Block submissionArtifact .Osaka 3647 (TnCacheRowTrace.middle) :=
  WindowTwentyOneSlice.block allWellFormed 2734 19 3647 (TnCacheRowTrace.middle)
    (by decide) (by rfl) (by rfl) (by decide)

def middleCopy : Block submissionArtifact .Osaka 5291 (TnCacheRowTrace.middle ++ [.push 2 3812, .op .JUMP]) :=
  WindowTwentyOneSlice.block allWellFormed 4053 21 5291 (TnCacheRowTrace.middle ++ [.push 2 3812, .op .JUMP])
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block submissionArtifact .Osaka 3912 (TnCacheRowTrace.tail) :=
  WindowTwentyOneSlice.block allWellFormed 2959 17 3912 (TnCacheRowTrace.tail)
    (by decide) (by rfl) (by rfl) (by decide)

def flush : Block submissionArtifact .Osaka 3963 (TnCacheFrameOps.flush) :=
  WindowTwentyOneSlice.block allWellFormed 2976 3 3963 (TnCacheFrameOps.flush)
    (by decide) (by rfl) (by rfl) (by decide)

def afterSquareReset : Block submissionArtifact .Osaka 3299 (TnCacheFrameOps.reset) :=
  WindowTwentyOneSlice.block allWellFormed 2448 3 3299 (TnCacheFrameOps.reset)
    (by decide) (by rfl) (by rfl) (by decide)

def againReset : Block submissionArtifact .Osaka 4077 (TnCacheFrameOps.reset) :=
  WindowTwentyOneSlice.block allWellFormed 3049 3 4077 (TnCacheFrameOps.reset)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks
