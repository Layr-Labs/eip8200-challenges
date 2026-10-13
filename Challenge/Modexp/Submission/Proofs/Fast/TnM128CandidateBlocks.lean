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

def l2Eight : Block submissionArtifact .Osaka 3843 (TnMod128Chain.fullProgram 8) :=
  WindowTwentyOneSlice.block allWellFormed 2990 201 3843 (TnMod128Chain.fullProgram 8)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Four : Block submissionArtifact .Osaka 3977 (TnMod128Chain.fullProgram 4) :=
  WindowTwentyOneSlice.block allWellFormed 3105 86 3977 (TnMod128Chain.fullProgram 4)
    (by decide) (by rfl) (by rfl) (by decide)

def cachedCell : Block submissionArtifact .Osaka 3912 (TnMod128Trace.program) :=
  WindowTwentyOneSlice.block allWellFormed 3049 28 3912 (TnMod128Trace.program)
    (by decide) (by rfl) (by rfl) (by decide)

def middle8 : Block submissionArtifact .Osaka 3822 (TnCacheRowTrace.middle8) :=
  WindowTwentyOneSlice.block allWellFormed 2970 20 3822 (TnCacheRowTrace.middle8)
    (by decide) (by rfl) (by rfl) (by decide)

def middleCopy : Block submissionArtifact .Osaka 5420 (TnCacheRowTrace.middle4 ++ [.push 3 3977, .op .JUMP]) :=
  WindowTwentyOneSlice.block allWellFormed 4259 21 5420 (TnCacheRowTrace.middle4 ++ [.push 3 3977, .op .JUMP])
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block submissionArtifact .Osaka 4077 (TnCacheRowTrace.tail) :=
  WindowTwentyOneSlice.block allWellFormed 3191 17 4077 (TnCacheRowTrace.tail)
    (by decide) (by rfl) (by rfl) (by decide)

def flush : Block submissionArtifact .Osaka 4128 (TnCacheFrameOps.flush13) :=
  WindowTwentyOneSlice.block allWellFormed 3208 3 4128 (TnCacheFrameOps.flush13)
    (by decide) (by rfl) (by rfl) (by decide)

def afterSquareReset : Block submissionArtifact .Osaka 3472 (TnCacheFrameOps.reset13) :=
  WindowTwentyOneSlice.block allWellFormed 2682 3 3472 (TnCacheFrameOps.reset13)
    (by decide) (by rfl) (by rfl) (by decide)

def againReset : Block submissionArtifact .Osaka 4199 (TnCacheFrameOps.reset13) :=
  WindowTwentyOneSlice.block allWellFormed 3258 3 4199 (TnCacheFrameOps.reset13)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks
