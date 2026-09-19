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

def l2Eight : Block submissionArtifact .Osaka 3851 (TnMod128Chain.fullProgram 8) :=
  WindowTwentyOneSlice.block allWellFormed 3083 206 3851 (TnMod128Chain.fullProgram 8)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Four : Block submissionArtifact .Osaka 3987 (TnMod128Chain.fullProgram 4) :=
  WindowTwentyOneSlice.block allWellFormed 3201 88 3987 (TnMod128Chain.fullProgram 4)
    (by decide) (by rfl) (by rfl) (by decide)

def cachedCell : Block submissionArtifact .Osaka 3922 (TnMod128Trace.program) :=
  WindowTwentyOneSlice.block allWellFormed 3144 29 3922 (TnMod128Trace.program)
    (by decide) (by rfl) (by rfl) (by decide)

def middle : Block submissionArtifact .Osaka 3832 (TnCacheRowTrace.middle) :=
  WindowTwentyOneSlice.block allWellFormed 3064 19 3832 (TnCacheRowTrace.middle)
    (by decide) (by rfl) (by rfl) (by decide)

def middleCopy : Block submissionArtifact .Osaka 5431 (TnCacheRowTrace.middle ++ [.push 2 3987, .op .JUMP]) :=
  WindowTwentyOneSlice.block allWellFormed 4357 21 5431 (TnCacheRowTrace.middle ++ [.push 2 3987, .op .JUMP])
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block submissionArtifact .Osaka 4087 (TnCacheRowTrace.tail) :=
  WindowTwentyOneSlice.block allWellFormed 3289 17 4087 (TnCacheRowTrace.tail)
    (by decide) (by rfl) (by rfl) (by decide)

def flush : Block submissionArtifact .Osaka 4138 (TnCacheFrameOps.flush) :=
  WindowTwentyOneSlice.block allWellFormed 3306 3 4138 (TnCacheFrameOps.flush)
    (by decide) (by rfl) (by rfl) (by decide)

def afterSquareReset : Block submissionArtifact .Osaka 3482 (TnCacheFrameOps.reset) :=
  WindowTwentyOneSlice.block allWellFormed 2776 3 3482 (TnCacheFrameOps.reset)
    (by decide) (by rfl) (by rfl) (by decide)

def againReset : Block submissionArtifact .Osaka 4252 (TnCacheFrameOps.reset) :=
  WindowTwentyOneSlice.block allWellFormed 3369 3 4252 (TnCacheFrameOps.reset)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks
