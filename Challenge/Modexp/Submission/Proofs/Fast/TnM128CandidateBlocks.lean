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

def l2Eight : Block submissionArtifact .Osaka 3841 (TnMod128Chain.fullProgram 8) :=
  WindowTwentyOneSlice.block allWellFormed 3067 205 3841 (TnMod128Chain.fullProgram 8)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Four : Block submissionArtifact .Osaka 3977 (TnMod128Chain.fullProgram 4) :=
  WindowTwentyOneSlice.block allWellFormed 3184 88 3977 (TnMod128Chain.fullProgram 4)
    (by decide) (by rfl) (by rfl) (by decide)

def cachedCell : Block submissionArtifact .Osaka 3912 (TnMod128Trace.program) :=
  WindowTwentyOneSlice.block allWellFormed 3128 28 3912 (TnMod128Trace.program)
    (by decide) (by rfl) (by rfl) (by decide)

def middle : Block submissionArtifact .Osaka 3822 (TnCacheRowTrace.middle) :=
  WindowTwentyOneSlice.block allWellFormed 3048 19 3822 (TnCacheRowTrace.middle)
    (by decide) (by rfl) (by rfl) (by decide)

def middleCopy : Block submissionArtifact .Osaka 5420 (TnCacheRowTrace.middle ++ [.push 3 3977, .op .JUMP]) :=
  WindowTwentyOneSlice.block allWellFormed 4339 21 5420 (TnCacheRowTrace.middle ++ [.push 3 3977, .op .JUMP])
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block submissionArtifact .Osaka 4077 (TnCacheRowTrace.tail) :=
  WindowTwentyOneSlice.block allWellFormed 3272 17 4077 (TnCacheRowTrace.tail)
    (by decide) (by rfl) (by rfl) (by decide)

def flush : Block submissionArtifact .Osaka 4128 (TnCacheFrameOps.flush) :=
  WindowTwentyOneSlice.block allWellFormed 3289 3 4128 (TnCacheFrameOps.flush)
    (by decide) (by rfl) (by rfl) (by decide)

def afterSquareReset : Block submissionArtifact .Osaka 3472 (TnCacheFrameOps.reset) :=
  WindowTwentyOneSlice.block allWellFormed 2761 3 3472 (TnCacheFrameOps.reset)
    (by decide) (by rfl) (by rfl) (by decide)

def againReset : Block submissionArtifact .Osaka 4242 (TnCacheFrameOps.reset) :=
  WindowTwentyOneSlice.block allWellFormed 3362 3 4242 (TnCacheFrameOps.reset)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks
